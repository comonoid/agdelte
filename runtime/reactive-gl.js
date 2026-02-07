/**
 * Agdelte WebGL Runtime
 *
 * Interprets Scott-encoded Scene values from Agdelte.WebGL.Types
 * and renders them using WebGL2. Supports:
 *   - Static geometry (box, sphere, plane, cylinder), transforms, cameras
 *   - Materials: unlit, flat (ambient-only), phong, pbr (Cook-Torrance), textured
 *   - Lights: ambient, directional, point, spot; bindLight (reactive)
 *   - Reactive bindings: bindTransform, bindMaterial, fromModel camera
 *   - Interaction: onClick, onHover, onLeave, onScroll via color picking
 *   - Ray casting: onClickAt (Vec3 hit point), onDrag (start+current Vec3)
 *   - Focus/keyboard: focusable, onKeyDown (KeyEvent), onInput (String)
 *   - Textures: loadTexture, textured material, icon (textured quad)
 *   - Custom geometry: BufferHandle, custom mesh data
 *   - Transitions: Duration, Easing (incl. cubicBezier), lerp/slerp
 *   - Continuous animation: animate node (Float time → Transform)
 *   - Transparency: painter's algorithm (opaque first, transparent back-to-front)
 *   - Canvas resize: ResizeObserver + HiDPI (devicePixelRatio)
 *
 * Integration:
 *   reactive.js creates <canvas> elements for glCanvas nodes and stores:
 *     canvas.__glScene    — the Scott-encoded Scene value
 *     canvas.__glDispatch — message dispatch function
 *     canvas.__glGetModel — function returning current model
 *     canvas.__glUpdate   — callback slot (set by this module)
 *
 * Color picking:
 *   Offscreen framebuffer renders each interactive object with a unique
 *   24-bit ID encoded as RGB. On click/mousemove, readPixels at cursor
 *   position → object ID → dispatch associated Msg.
 *
 * Render loop:
 *   IDLE      — no rAF, waiting for changes
 *   DIRTY     — changes pending, one rAF scheduled
 *   ANIMATING — active animations, rAF loop (future)
 */

// ---------------------------------------------------------------------------
// Scott-encoding interpreters
// ---------------------------------------------------------------------------

/**
 * Interpret a Scott-encoded Scene into a plain JS object.
 * Returns { camera, nodes } where camera/nodes contain binding info.
 */
function interpretScene(scene) {
  return scene({
    mkScene: (camera, nodes) => ({ camera, nodes })
  });
}

/**
 * Interpret Camera. Returns either:
 *   { type: 'fixed', projection, pos, target }
 *   { type: 'fromModel', projExtract, posExtract, targetExtract }
 */
function interpretCamera(camera) {
  return camera({
    fixed: (projection, pos, target) => ({
      type: 'fixed',
      projection: interpretProjection(projection),
      pos, target
    }),
    fromModel: (projExtract, posExtract, targetExtract) => ({
      type: 'fromModel',
      projExtract, posExtract, targetExtract
    })
  });
}

function interpretProjection(projection) {
  return projection({
    perspective: (fov, near, far) => ({
      type: 'perspective', fov, near, far
    }),
    orthographic: (size, near, far) => ({
      type: 'orthographic', size, near, far
    })
  });
}

/**
 * Interpret a SceneNode into a render node.
 * Render nodes carry binding functions for reactive updates.
 *
 * Render node types:
 *   { type: 'mesh', geometry, material, attrs, transform }
 *   { type: 'group', transform, children }
 *   { type: 'bindTransform', extract, child }
 *   { type: 'bindMaterial', extract, geometry, attrs, transform }
 */
function interpretSceneNode(node) {
  return node({
    mesh: (geometry, material, attrs, transform) => ({
      type: 'mesh',
      geometry: interpretGeometry(geometry),
      material: interpretMaterial(material),
      attrs: listToArray(attrs).map(interpretSceneAttr),
      transform: interpretTransform(transform)
    }),
    group: (transform, children) => ({
      type: 'group',
      transform: interpretTransform(transform),
      children: listToArray(children).map(interpretSceneNode)
    }),
    icon: (texHandle, size, attrs, transform) => ({
      type: 'icon',
      url: texHandle,  // loadTexture compiles to identity, so texHandle is a URL string
      size,            // Vec2 { x, y }
      attrs: listToArray(attrs).map(interpretSceneAttr),
      transform: interpretTransform(transform)
    }),
    light: (lightVal) => ({
      type: 'light',
      light: interpretLight(lightVal)
    }),
    bindTransform: (extract, child) => ({
      type: 'bindTransform',
      extract,           // Model → Transform (Scott-encoded)
      child: interpretSceneNode(child)
    }),
    bindMaterial: (extract, geometry, attrs, transform) => ({
      type: 'bindMaterial',
      extract,           // Model → Material (Scott-encoded)
      geometry: interpretGeometry(geometry),
      attrs: listToArray(attrs).map(interpretSceneAttr),
      transform: interpretTransform(transform)
    }),
    text3D: (str, style, attrs, transform) => ({
      type: 'text3D',
      text: str,
      style: interpretTextStyle(style),
      attrs: listToArray(attrs).map(interpretSceneAttr),
      transform: interpretTransform(transform)
    }),
    bindText3D: (extract, style, attrs, transform) => ({
      type: 'bindText3D',
      extract,           // Model → String
      style: interpretTextStyle(style),
      attrs: listToArray(attrs).map(interpretSceneAttr),
      transform: interpretTransform(transform)
    }),
    bindLight: (extract) => ({
      type: 'bindLight',
      extract,           // Model → Light (Scott-encoded)
    }),
    animate: (timeFn, child) => ({
      type: 'animate',
      timeFn,            // Float → Transform (Scott-encoded)
      child: interpretSceneNode(child)
    })
  });
}

/**
 * Interpret a Scott-encoded TextStyle.
 */
function interpretTextStyle(style) {
  return style({
    mkTextStyle: (font, size, color, align, layout) => ({
      font: interpretFontRef(font),
      size,
      color,   // GlColor { r, g, b, a }
      align: interpretAlign(align),
      layout: interpretTextLayout(layout)
    })
  });
}

function interpretFontRef(font) {
  return font({
    builtin: (builtinFont) => builtinFont({
      sans: () => ({ type: 'builtin', name: 'sans' }),
      mono: () => ({ type: 'builtin', name: 'mono' }),
    }),
    custom: (url) => ({ type: 'custom', url })
  });
}

function interpretAlign(align) {
  return align({
    left:   () => 'left',
    center: () => 'center',
    right:  () => 'right',
  });
}

function interpretTextLayout(layout) {
  return layout({
    singleLine: () => ({ type: 'singleLine' }),
    wrapAt:     (maxWidth) => ({ type: 'wrapAt', maxWidth }),
    ellipsis:   (maxWidth) => ({ type: 'ellipsis', maxWidth }),
  });
}

/**
 * Interpret a SceneAttr into a plain event descriptor.
 * Returns { type: 'onClick'|'onHover'|'onLeave'|'transition', ... }
 */
function interpretSceneAttr(attr) {
  return attr({
    onClick: (msg) => ({ type: 'onClick', msg }),
    onHover: (msg) => ({ type: 'onHover', msg }),
    onLeave: (msg) => ({ type: 'onLeave', msg }),
    onScroll: (handler) => ({ type: 'onScroll', handler }),
    onClickAt: (handler) => ({ type: 'onClickAt', handler }),
    onDrag: (handler) => ({ type: 'onDrag', handler }),
    focusable: () => ({ type: 'focusable' }),
    onKeyDown: (handler) => ({ type: 'onKeyDown', handler }),
    onInput: (handler) => ({ type: 'onInput', handler }),
    transition: (duration, easing) => ({
      type: 'transition',
      durationMs: interpretDuration(duration),
      easing: interpretEasing(easing)
    })
  });
}

/**
 * Interpret a Scott-encoded Duration.
 * Duration.ms wraps a Scott-encoded ℕ.
 */
function interpretDuration(dur) {
  return dur({
    ms: (n) => scottNatToNumber(n)
  });
}

/**
 * Interpret a Scott-encoded Easing into a string tag.
 */
function interpretEasing(easing) {
  return easing({
    linear:      () => 'linear',
    easeIn:      () => 'easeIn',
    easeOut:     () => 'easeOut',
    easeInOut:   () => 'easeInOut',
    cubicBezier: (x1, y1, x2, y2) => ({ type: 'cubicBezier', x1, y1, x2, y2 })
  });
}

/**
 * Convert an Agda ℕ to a JS number.
 * The Agda JS backend may represent ℕ as:
 *   - BigInt (for literals like 300)
 *   - Scott-encoded (for computed values: zero/suc)
 */
function scottNatToNumber(n) {
  // BigInt (optimized literal)
  if (typeof n === 'bigint') return Number(n);
  // Plain number
  if (typeof n === 'number') return n;
  // Scott-encoded: walk zero/suc chain
  let result = 0;
  let current = n;
  for (let i = 0; i < 100000; i++) {
    let done = false;
    current({
      'zero': () => { done = true; },
      'suc': (pred) => { result++; current = pred; }
    });
    if (done) break;
  }
  return result;
}

/**
 * Interpret a Light into a plain JS object.
 * Returns { type: 'ambient'|'directional', color, intensity, direction? }
 */
function interpretLight(light) {
  return light({
    ambient: (color, intensity) => ({
      type: 'ambient', color, intensity
    }),
    directional: (color, intensity, direction) => ({
      type: 'directional', color, intensity, direction
    }),
    point: (color, intensity, position, range) => ({
      type: 'point', color, intensity, position, range
    }),
    spot: (color, intensity, pos, dir, angle, falloff) => ({
      type: 'spot', color, intensity, pos, dir, angle, falloff
    })
  });
}

function interpretGeometry(geom) {
  return geom({
    box:      (dims) => ({ type: 'box', dims }),
    sphere:   (radius) => ({ type: 'sphere', radius }),
    plane:    (size) => ({ type: 'plane', size }),
    cylinder: (radius, height) => ({ type: 'cylinder', radius, height }),
    custom:   (handle) => ({ type: 'custom', handle })
  });
}

function interpretMaterial(mat) {
  return mat({
    unlit:    (color) => ({ type: 'unlit', color }),
    flat:     (color) => ({ type: 'flat', color }),
    phong:    (color, shininess) => ({ type: 'phong', color, shininess }),
    pbr:      (color, metallic, roughness) => ({ type: 'pbr', color, metallic, roughness }),
    textured: (texHandle, tint) => ({ type: 'textured', url: texHandle, tint })
  });
}

function interpretTransform(tfm) {
  return tfm({
    mkTransform: (pos, rot, scale) => ({ pos, rot, scale })
  });
}

/** Convert Agda List to JS Array */
function listToArray(list) {
  if (!list) return [];
  if (Array.isArray(list)) return list;
  const items = [];
  let current = list;
  const MAX = 10000;
  for (let i = 0; i < MAX; i++) {
    let done = false;
    current({
      '[]': () => { done = true; },
      '_∷_': (head, tail) => {
        items.push(head);
        current = tail;
      }
    });
    if (done) break;
  }
  return items;
}

// ---------------------------------------------------------------------------
// Shader sources
// ---------------------------------------------------------------------------

const VERT_SRC = `#version 300 es
precision highp float;

layout(location = 0) in vec3 a_position;
layout(location = 1) in vec3 a_normal;

uniform mat4 u_model;
uniform mat4 u_view;
uniform mat4 u_proj;

out vec3 v_normal;

void main() {
  v_normal = mat3(u_model) * a_normal;
  gl_Position = u_proj * u_view * u_model * vec4(a_position, 1.0);
}
`;

const FRAG_SRC = `#version 300 es
precision highp float;

uniform vec4 u_color;

out vec4 fragColor;

void main() {
  fragColor = u_color;
}
`;

// Phong shader — Blinn-Phong lighting with ambient + directional lights
const PHONG_VERT_SRC = `#version 300 es
precision highp float;

layout(location = 0) in vec3 a_position;
layout(location = 1) in vec3 a_normal;

uniform mat4 u_model;
uniform mat4 u_view;
uniform mat4 u_proj;

out vec3 v_normal;
out vec3 v_worldPos;

void main() {
  vec4 worldPos = u_model * vec4(a_position, 1.0);
  v_worldPos = worldPos.xyz;
  v_normal = normalize(mat3(u_model) * a_normal);
  gl_Position = u_proj * u_view * worldPos;
}
`;

const PHONG_FRAG_SRC = `#version 300 es
precision highp float;

uniform vec4 u_color;
uniform float u_shininess;
uniform vec3 u_cameraPos;
uniform int u_flatMode;              // 1 = flat material (ambient only)

// Lights: up to 8
uniform int u_numLights;
uniform int u_lightType[8];         // 0=ambient, 1=directional, 2=point, 3=spot
uniform vec3 u_lightColor[8];
uniform float u_lightIntensity[8];
uniform vec3 u_lightDir[8];         // direction (directional/spot)
uniform vec3 u_lightPos[8];         // position (point/spot)
uniform float u_lightRange[8];      // range (point/spot)
uniform float u_lightAngle[8];      // cone angle in radians (spot)
uniform float u_lightFalloff[8];    // edge falloff (spot)

in vec3 v_normal;
in vec3 v_worldPos;

out vec4 fragColor;

void main() {
  vec3 N = normalize(v_normal);
  vec3 V = normalize(u_cameraPos - v_worldPos);
  vec3 result = vec3(0.0);

  for (int i = 0; i < 8; i++) {
    if (i >= u_numLights) break;

    vec3 lc = u_lightColor[i] * u_lightIntensity[i];

    if (u_lightType[i] == 0) {
      // Ambient
      result += u_color.rgb * lc;
    } else if (u_flatMode == 1) {
      // Flat material: skip non-ambient lights
      continue;
    } else if (u_lightType[i] == 1) {
      // Directional (Blinn-Phong)
      vec3 L = normalize(-u_lightDir[i]);
      float diff = max(dot(N, L), 0.0);
      vec3 H = normalize(L + V);
      float spec = pow(max(dot(N, H), 0.0), u_shininess);
      result += u_color.rgb * lc * diff + lc * spec;
    } else if (u_lightType[i] == 2) {
      // Point light
      vec3 toLight = u_lightPos[i] - v_worldPos;
      float dist = length(toLight);
      vec3 L = toLight / max(dist, 0.001);
      float atten = clamp(1.0 - dist / max(u_lightRange[i], 0.001), 0.0, 1.0);
      atten *= atten;  // quadratic falloff
      float diff = max(dot(N, L), 0.0);
      vec3 H = normalize(L + V);
      float spec = pow(max(dot(N, H), 0.0), u_shininess);
      result += (u_color.rgb * lc * diff + lc * spec) * atten;
    } else if (u_lightType[i] == 3) {
      // Spot light
      vec3 toLight = u_lightPos[i] - v_worldPos;
      float dist = length(toLight);
      vec3 L = toLight / max(dist, 0.001);
      float atten = clamp(1.0 - dist / max(u_lightRange[i], 0.001), 0.0, 1.0);
      atten *= atten;
      // Cone attenuation
      vec3 spotDir = normalize(u_lightDir[i]);
      float cosAngle = dot(-L, spotDir);
      float cosOuter = cos(u_lightAngle[i]);
      float cosInner = cos(u_lightAngle[i] * (1.0 - u_lightFalloff[i]));
      float spotAtten = clamp((cosAngle - cosOuter) / max(cosInner - cosOuter, 0.001), 0.0, 1.0);
      atten *= spotAtten;
      float diff = max(dot(N, L), 0.0);
      vec3 H = normalize(L + V);
      float spec = pow(max(dot(N, H), 0.0), u_shininess);
      result += (u_color.rgb * lc * diff + lc * spec) * atten;
    }
  }

  fragColor = vec4(result, u_color.a);
}
`;

// Picking shader — renders each object with a unique RGB ID
const PICK_VERT_SRC = `#version 300 es
precision highp float;

layout(location = 0) in vec3 a_position;

uniform mat4 u_model;
uniform mat4 u_view;
uniform mat4 u_proj;

void main() {
  gl_Position = u_proj * u_view * u_model * vec4(a_position, 1.0);
}
`;

const PICK_FRAG_SRC = `#version 300 es
precision highp float;

uniform vec3 u_objectId;

out vec4 fragColor;

void main() {
  fragColor = vec4(u_objectId, 1.0);
}
`;

// PBR shader — Cook-Torrance BRDF with metallic/roughness workflow
const PBR_VERT_SRC = PHONG_VERT_SRC;  // same vertex shader as phong

const PBR_FRAG_SRC = `#version 300 es
precision highp float;

uniform vec4 u_color;        // albedo
uniform float u_metallic;
uniform float u_roughness;
uniform vec3 u_cameraPos;

// Lights: up to 8
uniform int u_numLights;
uniform int u_lightType[8];
uniform vec3 u_lightColor[8];
uniform float u_lightIntensity[8];
uniform vec3 u_lightDir[8];
uniform vec3 u_lightPos[8];
uniform float u_lightRange[8];
uniform float u_lightAngle[8];
uniform float u_lightFalloff[8];

in vec3 v_normal;
in vec3 v_worldPos;

out vec4 fragColor;

const float PI = 3.14159265359;

// GGX/Trowbridge-Reitz normal distribution
float D_GGX(float NdotH, float a) {
  float a2 = a * a;
  float d = NdotH * NdotH * (a2 - 1.0) + 1.0;
  return a2 / (PI * d * d);
}

// Schlick-GGX geometry function
float G_SchlickGGX(float NdotV, float k) {
  return NdotV / (NdotV * (1.0 - k) + k);
}

float G_Smith(float NdotV, float NdotL, float roughness) {
  float k = (roughness + 1.0) * (roughness + 1.0) / 8.0;
  return G_SchlickGGX(NdotV, k) * G_SchlickGGX(NdotL, k);
}

// Fresnel-Schlick approximation
vec3 F_Schlick(float cosTheta, vec3 F0) {
  return F0 + (1.0 - F0) * pow(1.0 - cosTheta, 5.0);
}

void main() {
  vec3 N = normalize(v_normal);
  vec3 V = normalize(u_cameraPos - v_worldPos);
  float NdotV = max(dot(N, V), 0.001);

  vec3 albedo = u_color.rgb;
  vec3 F0 = mix(vec3(0.04), albedo, u_metallic);
  float alpha = u_roughness * u_roughness;

  vec3 Lo = vec3(0.0);

  for (int i = 0; i < 8; i++) {
    if (i >= u_numLights) break;

    vec3 lc = u_lightColor[i] * u_lightIntensity[i];

    if (u_lightType[i] == 0) {
      // Ambient
      Lo += albedo * lc;
      continue;
    }

    vec3 L;
    float atten = 1.0;

    if (u_lightType[i] == 1) {
      L = normalize(-u_lightDir[i]);
    } else if (u_lightType[i] == 2) {
      vec3 toLight = u_lightPos[i] - v_worldPos;
      float dist = length(toLight);
      L = toLight / max(dist, 0.001);
      atten = clamp(1.0 - dist / max(u_lightRange[i], 0.001), 0.0, 1.0);
      atten *= atten;
    } else if (u_lightType[i] == 3) {
      vec3 toLight = u_lightPos[i] - v_worldPos;
      float dist = length(toLight);
      L = toLight / max(dist, 0.001);
      atten = clamp(1.0 - dist / max(u_lightRange[i], 0.001), 0.0, 1.0);
      atten *= atten;
      vec3 spotDir = normalize(u_lightDir[i]);
      float cosAngle = dot(-L, spotDir);
      float cosOuter = cos(u_lightAngle[i]);
      float cosInner = cos(u_lightAngle[i] * (1.0 - u_lightFalloff[i]));
      atten *= clamp((cosAngle - cosOuter) / max(cosInner - cosOuter, 0.001), 0.0, 1.0);
    } else {
      continue;
    }

    vec3 H = normalize(V + L);
    float NdotL = max(dot(N, L), 0.0);
    float NdotH = max(dot(N, H), 0.0);
    float HdotV = max(dot(H, V), 0.0);

    float D = D_GGX(NdotH, alpha);
    float G = G_Smith(NdotV, NdotL, u_roughness);
    vec3  F = F_Schlick(HdotV, F0);

    vec3 specular = (D * G * F) / max(4.0 * NdotV * NdotL, 0.001);
    vec3 kD = (vec3(1.0) - F) * (1.0 - u_metallic);
    Lo += (kD * albedo / PI + specular) * lc * NdotL * atten;
  }

  fragColor = vec4(Lo, u_color.a);
}
`;

// Textured shader — samples texture, multiplied by tint color
const TEX_VERT_SRC = `#version 300 es
precision highp float;

layout(location = 0) in vec3 a_position;
layout(location = 1) in vec3 a_normal;
layout(location = 2) in vec2 a_uv;

uniform mat4 u_model;
uniform mat4 u_view;
uniform mat4 u_proj;

out vec2 v_uv;

void main() {
  v_uv = a_uv;
  gl_Position = u_proj * u_view * u_model * vec4(a_position, 1.0);
}
`;

const TEX_FRAG_SRC = `#version 300 es
precision highp float;

uniform sampler2D u_texture;
uniform vec4 u_color;  // tint

in vec2 v_uv;

out vec4 fragColor;

void main() {
  vec4 texColor = texture(u_texture, v_uv);
  fragColor = texColor * u_color;
}
`;

// ---------------------------------------------------------------------------
// Math utilities (column-major 4x4 matrices)
// ---------------------------------------------------------------------------

function mat4Identity() {
  return new Float32Array([
    1, 0, 0, 0,
    0, 1, 0, 0,
    0, 0, 1, 0,
    0, 0, 0, 1
  ]);
}

function mat4Ortho(size, aspect, near, far) {
  const right = size * aspect * 0.5;
  const left = -right;
  const top = size * 0.5;
  const bottom = -top;
  const lr = 1 / (left - right);
  const bt = 1 / (bottom - top);
  const nf = 1 / (near - far);
  const out = new Float32Array(16);
  out[0]  = -2 * lr;
  out[5]  = -2 * bt;
  out[10] = 2 * nf;
  out[12] = (left + right) * lr;
  out[13] = (top + bottom) * bt;
  out[14] = (far + near) * nf;
  out[15] = 1;
  return out;
}

function mat4Perspective(fov, aspect, near, far) {
  const f = 1.0 / Math.tan(fov * 0.5);
  const nf = 1 / (near - far);
  const out = new Float32Array(16);
  out[0]  = f / aspect;
  out[5]  = f;
  out[10] = (far + near) * nf;
  out[11] = -1;
  out[14] = 2 * far * near * nf;
  return out;
}

function mat4LookAt(eye, target, up) {
  const zx = eye.x - target.x;
  const zy = eye.y - target.y;
  const zz = eye.z - target.z;
  let len = Math.hypot(zx, zy, zz);
  const iz = len ? 1 / len : 0;
  const fz = { x: zx * iz, y: zy * iz, z: zz * iz };

  // cross(up, fz)
  const xx = up.y * fz.z - up.z * fz.y;
  const xy = up.z * fz.x - up.x * fz.z;
  const xz = up.x * fz.y - up.y * fz.x;
  len = Math.hypot(xx, xy, xz);
  const ix = len ? 1 / len : 0;
  const fx = { x: xx * ix, y: xy * ix, z: xz * ix };

  // cross(fz, fx)
  const yx = fz.y * fx.z - fz.z * fx.y;
  const yy = fz.z * fx.x - fz.x * fx.z;
  const yz = fz.x * fx.y - fz.y * fx.x;

  const out = new Float32Array(16);
  out[0] = fx.x; out[1] = yx;   out[2]  = fz.x; out[3]  = 0;
  out[4] = fx.y; out[5] = yy;   out[6]  = fz.y; out[7]  = 0;
  out[8] = fx.z; out[9] = yz;   out[10] = fz.z; out[11] = 0;
  out[12] = -(fx.x * eye.x + fx.y * eye.y + fx.z * eye.z);
  out[13] = -(yx * eye.x + yy * eye.y + yz * eye.z);
  out[14] = -(fz.x * eye.x + fz.y * eye.y + fz.z * eye.z);
  out[15] = 1;
  return out;
}

function mat4FromTRS(pos, rot, scale) {
  const x = rot.x, y = rot.y, z = rot.z, w = rot.w;
  const x2 = x + x, y2 = y + y, z2 = z + z;
  const xx = x * x2, xy = x * y2, xz = x * z2;
  const yy = y * y2, yz = y * z2, zz = z * z2;
  const wx = w * x2, wy = w * y2, wz = w * z2;

  const sx = scale.x, sy = scale.y, sz = scale.z;

  const out = new Float32Array(16);
  out[0]  = (1 - (yy + zz)) * sx;
  out[1]  = (xy + wz) * sx;
  out[2]  = (xz - wy) * sx;
  out[3]  = 0;
  out[4]  = (xy - wz) * sy;
  out[5]  = (1 - (xx + zz)) * sy;
  out[6]  = (yz + wx) * sy;
  out[7]  = 0;
  out[8]  = (xz + wy) * sz;
  out[9]  = (yz - wx) * sz;
  out[10] = (1 - (xx + yy)) * sz;
  out[11] = 0;
  out[12] = pos.x;
  out[13] = pos.y;
  out[14] = pos.z;
  out[15] = 1;
  return out;
}

function mat4Multiply(a, b) {
  const out = new Float32Array(16);
  for (let i = 0; i < 4; i++) {
    for (let j = 0; j < 4; j++) {
      out[j * 4 + i] =
        a[0 * 4 + i] * b[j * 4 + 0] +
        a[1 * 4 + i] * b[j * 4 + 1] +
        a[2 * 4 + i] * b[j * 4 + 2] +
        a[3 * 4 + i] * b[j * 4 + 3];
    }
  }
  return out;
}

/**
 * Invert a 4x4 matrix (column-major Float32Array). Returns null if singular.
 */
function mat4Invert(m) {
  const a00 = m[0], a01 = m[1], a02 = m[2], a03 = m[3];
  const a10 = m[4], a11 = m[5], a12 = m[6], a13 = m[7];
  const a20 = m[8], a21 = m[9], a22 = m[10], a23 = m[11];
  const a30 = m[12], a31 = m[13], a32 = m[14], a33 = m[15];

  const b00 = a00 * a11 - a01 * a10;
  const b01 = a00 * a12 - a02 * a10;
  const b02 = a00 * a13 - a03 * a10;
  const b03 = a01 * a12 - a02 * a11;
  const b04 = a01 * a13 - a03 * a11;
  const b05 = a02 * a13 - a03 * a12;
  const b06 = a20 * a31 - a21 * a30;
  const b07 = a20 * a32 - a22 * a30;
  const b08 = a20 * a33 - a23 * a30;
  const b09 = a21 * a32 - a22 * a31;
  const b10 = a21 * a33 - a23 * a31;
  const b11 = a22 * a33 - a23 * a32;

  let det = b00 * b11 - b01 * b10 + b02 * b09 + b03 * b08 - b04 * b07 + b05 * b06;
  if (Math.abs(det) < 1e-10) return null;
  det = 1.0 / det;

  const out = new Float32Array(16);
  out[0]  = (a11 * b11 - a12 * b10 + a13 * b09) * det;
  out[1]  = (a02 * b10 - a01 * b11 - a03 * b09) * det;
  out[2]  = (a31 * b05 - a32 * b04 + a33 * b03) * det;
  out[3]  = (a22 * b04 - a21 * b05 - a23 * b03) * det;
  out[4]  = (a12 * b08 - a10 * b11 - a13 * b07) * det;
  out[5]  = (a00 * b11 - a02 * b08 + a03 * b07) * det;
  out[6]  = (a32 * b02 - a30 * b05 - a33 * b01) * det;
  out[7]  = (a20 * b05 - a22 * b02 + a23 * b01) * det;
  out[8]  = (a10 * b10 - a11 * b08 + a13 * b06) * det;
  out[9]  = (a01 * b08 - a00 * b10 - a03 * b06) * det;
  out[10] = (a30 * b04 - a31 * b02 + a33 * b00) * det;
  out[11] = (a21 * b02 - a20 * b04 - a23 * b00) * det;
  out[12] = (a11 * b07 - a10 * b09 - a12 * b06) * det;
  out[13] = (a00 * b09 - a01 * b07 + a02 * b06) * det;
  out[14] = (a31 * b01 - a30 * b03 - a32 * b00) * det;
  out[15] = (a20 * b03 - a21 * b01 + a22 * b00) * det;
  return out;
}

/**
 * Unproject a screen point (NDC x,y in [-1,1], z in [-1,1]) to world space.
 * Returns { x, y, z } or null if matrices are singular.
 */
function unprojectPoint(ndcX, ndcY, ndcZ, projMat, viewMat) {
  const vp = mat4Multiply(projMat, viewMat);
  const inv = mat4Invert(vp);
  if (!inv) return null;
  // Homogeneous clip space
  const hx = ndcX, hy = ndcY, hz = ndcZ, hw = 1.0;
  const wx = inv[0] * hx + inv[4] * hy + inv[8]  * hz + inv[12] * hw;
  const wy = inv[1] * hx + inv[5] * hy + inv[9]  * hz + inv[13] * hw;
  const wz = inv[2] * hx + inv[6] * hy + inv[10] * hz + inv[14] * hw;
  const ww = inv[3] * hx + inv[7] * hy + inv[11] * hz + inv[15] * hw;
  if (Math.abs(ww) < 1e-10) return null;
  return { x: wx / ww, y: wy / ww, z: wz / ww };
}

/**
 * Build a ray from screen coordinates.
 * Returns { origin: Vec3, dir: Vec3 } — dir is normalized.
 * cssX/cssY are in CSS pixels relative to the canvas element.
 */
function screenToRay(cssX, cssY, canvas, projMat, viewMat) {
  const rect = canvas.getBoundingClientRect();
  const ndcX = ((cssX - rect.left) / rect.width) * 2 - 1;
  const ndcY = 1 - ((cssY - rect.top) / rect.height) * 2;
  const near = unprojectPoint(ndcX, ndcY, -1, projMat, viewMat);
  const far  = unprojectPoint(ndcX, ndcY,  1, projMat, viewMat);
  if (!near || !far) return null;
  const dx = far.x - near.x, dy = far.y - near.y, dz = far.z - near.z;
  const len = Math.hypot(dx, dy, dz);
  if (len < 1e-10) return null;
  return { origin: near, dir: { x: dx / len, y: dy / len, z: dz / len } };
}

/**
 * Ray-sphere intersection. Returns t (distance along ray) or null.
 * Sphere at center with given radius.
 */
function raySphere(ray, center, radius) {
  const ox = ray.origin.x - center.x;
  const oy = ray.origin.y - center.y;
  const oz = ray.origin.z - center.z;
  const a = ray.dir.x ** 2 + ray.dir.y ** 2 + ray.dir.z ** 2;
  const b = 2 * (ox * ray.dir.x + oy * ray.dir.y + oz * ray.dir.z);
  const c = ox ** 2 + oy ** 2 + oz ** 2 - radius * radius;
  const disc = b * b - 4 * a * c;
  if (disc < 0) return null;
  const sqrtD = Math.sqrt(disc);
  const t0 = (-b - sqrtD) / (2 * a);
  const t1 = (-b + sqrtD) / (2 * a);
  if (t0 >= 0) return t0;
  if (t1 >= 0) return t1;
  return null;
}

/**
 * Ray-AABB intersection (axis-aligned box centered at origin with half-extents).
 * The box is in local space; transform ray to local space before calling.
 */
function rayAABB(ray, halfX, halfY, halfZ) {
  let tmin = -Infinity, tmax = Infinity;
  const axes = [
    { o: ray.origin.x, d: ray.dir.x, h: halfX },
    { o: ray.origin.y, d: ray.dir.y, h: halfY },
    { o: ray.origin.z, d: ray.dir.z, h: halfZ },
  ];
  for (const { o, d, h } of axes) {
    if (Math.abs(d) < 1e-10) {
      if (o < -h || o > h) return null;
    } else {
      let t1 = (-h - o) / d;
      let t2 = ( h - o) / d;
      if (t1 > t2) { const tmp = t1; t1 = t2; t2 = tmp; }
      tmin = Math.max(tmin, t1);
      tmax = Math.min(tmax, t2);
      if (tmin > tmax) return null;
    }
  }
  return tmin >= 0 ? tmin : (tmax >= 0 ? tmax : null);
}

/**
 * Ray-plane intersection (XZ plane at y=0 in local space).
 */
function rayPlane(ray) {
  if (Math.abs(ray.dir.y) < 1e-10) return null;
  const t = -ray.origin.y / ray.dir.y;
  return t >= 0 ? t : null;
}

/**
 * Transform a ray to local space given a model matrix.
 * Returns a new ray with origin and dir in the object's local coordinate system.
 */
function rayToLocal(ray, modelMat) {
  const inv = mat4Invert(modelMat);
  if (!inv) return null;
  // Transform origin (point: w=1)
  const ox = inv[0] * ray.origin.x + inv[4] * ray.origin.y + inv[8]  * ray.origin.z + inv[12];
  const oy = inv[1] * ray.origin.x + inv[5] * ray.origin.y + inv[9]  * ray.origin.z + inv[13];
  const oz = inv[2] * ray.origin.x + inv[6] * ray.origin.y + inv[10] * ray.origin.z + inv[14];
  // Transform direction (vector: w=0)
  const dx = inv[0] * ray.dir.x + inv[4] * ray.dir.y + inv[8]  * ray.dir.z;
  const dy = inv[1] * ray.dir.x + inv[5] * ray.dir.y + inv[9]  * ray.dir.z;
  const dz = inv[2] * ray.dir.x + inv[6] * ray.dir.y + inv[10] * ray.dir.z;
  const len = Math.hypot(dx, dy, dz);
  if (len < 1e-10) return null;
  return {
    origin: { x: ox, y: oy, z: oz },
    dir: { x: dx / len, y: dy / len, z: dz / len },
    // Keep the scale factor so we can convert local t back to world t
    scale: len
  };
}

/**
 * Compute world-space hit point given ray and distance t.
 */
function rayAt(ray, t) {
  return {
    x: ray.origin.x + ray.dir.x * t,
    y: ray.origin.y + ray.dir.y * t,
    z: ray.origin.z + ray.dir.z * t
  };
}

/**
 * Intersect a ray with a render entry's geometry in world space.
 * Returns { t, point } or null. parentMat is the accumulated model matrix.
 */
function rayIntersectEntry(ray, entry, parentMat) {
  if (entry.type === 'mesh') {
    const tfm = entry.transform;
    const modelMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);

    const localRay = rayToLocal(ray, modelMat);
    if (!localRay) return null;

    let localT = null;
    const geo = entry.geometry;

    switch (geo.type) {
      case 'sphere': {
        // Unit sphere (radius 1) in local space, scaled by transform
        localT = raySphere(localRay, { x: 0, y: 0, z: 0 }, 1.0);
        break;
      }
      case 'box': {
        // Box geometry dims are full width; half-extents = dims/2
        // In local space the box is centered at origin with half-extents 0.5
        // (the TRS scale already accounts for dims)
        localT = rayAABB(localRay, 0.5, 0.5, 0.5);
        break;
      }
      case 'cylinder': {
        // Approximate cylinder as a box for now (height along Y)
        localT = rayAABB(localRay, 0.5, 0.5, 0.5);
        break;
      }
      case 'plane': {
        localT = rayPlane(localRay);
        // Check bounds: plane goes from -0.5 to 0.5 in X and Z
        if (localT !== null) {
          const lp = rayAt(localRay, localT);
          if (Math.abs(lp.x) > 0.5 || Math.abs(lp.z) > 0.5) localT = null;
        }
        break;
      }
      case 'quad': {
        localT = rayPlane(localRay);
        if (localT !== null) {
          const lp = rayAt(localRay, localT);
          if (Math.abs(lp.x) > 0.5 || Math.abs(lp.z) > 0.5) localT = null;
        }
        break;
      }
      default:
        // custom geometry — no analytical intersection
        return null;
    }

    if (localT === null) return null;
    // Convert local t to world t (approximate: divide by scale factor)
    const worldT = localT / localRay.scale;
    const point = rayAt(ray, worldT);
    return { t: worldT, point };

  } else if (entry.type === 'group') {
    const tfm = entry.transform;
    const groupMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);

    let closest = null;
    for (const child of entry.children) {
      const hit = rayIntersectEntry(ray, child, groupMat);
      if (hit && (!closest || hit.t < closest.t)) {
        closest = hit;
      }
    }
    return closest;
  }
  return null;
}

/**
 * Find the closest ray-intersected pickable entry.
 * Returns { pickId, point } or null.
 */
function rayPickEntries(ray, renderList, pickRegistry) {
  let closest = null;
  let closestPickId = 0;

  for (const entry of renderList) {
    if (entry.type === 'mesh' && entry.pickId != null) {
      const hit = rayIntersectEntry(ray, entry, null);
      if (hit && (!closest || hit.t < closest.t)) {
        closest = hit;
        closestPickId = entry.pickId;
      }
    } else if (entry.type === 'group') {
      // For groups, we need to check children with pickIds
      const groupHits = [];
      rayPickGroup(ray, entry, null, groupHits);
      for (const gh of groupHits) {
        if (!closest || gh.t < closest.t) {
          closest = gh;
          closestPickId = gh.pickId;
        }
      }
    }
  }

  if (!closest) return null;
  return { pickId: closestPickId, point: closest.point };
}

/**
 * Recursively find ray hits in a group, collecting { t, point, pickId }.
 */
function rayPickGroup(ray, entry, parentMat, results) {
  if (entry.type === 'mesh') {
    const hit = rayIntersectEntry(ray, entry, parentMat);
    if (hit && entry.pickId != null) {
      results.push({ t: hit.t, point: hit.point, pickId: entry.pickId });
    }
  } else if (entry.type === 'group') {
    const tfm = entry.transform;
    const groupMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);
    for (const child of entry.children) {
      rayPickGroup(ray, child, groupMat, results);
    }
  }
}

// ---------------------------------------------------------------------------
// Geometry generation
// ---------------------------------------------------------------------------

function createBoxGeometry(gl, dims) {
  const hw = dims.x * 0.5, hh = dims.y * 0.5, hd = dims.z * 0.5;
  const positions = new Float32Array([
    -hw, -hh,  hd,   hw, -hh,  hd,   hw,  hh,  hd,  -hw,  hh,  hd,
     hw, -hh, -hd,  -hw, -hh, -hd,  -hw,  hh, -hd,   hw,  hh, -hd,
    -hw,  hh,  hd,   hw,  hh,  hd,   hw,  hh, -hd,  -hw,  hh, -hd,
    -hw, -hh, -hd,   hw, -hh, -hd,   hw, -hh,  hd,  -hw, -hh,  hd,
     hw, -hh,  hd,   hw, -hh, -hd,   hw,  hh, -hd,   hw,  hh,  hd,
    -hw, -hh, -hd,  -hw, -hh,  hd,  -hw,  hh,  hd,  -hw,  hh, -hd,
  ]);
  const normals = new Float32Array([
    0, 0, 1,  0, 0, 1,  0, 0, 1,  0, 0, 1,
    0, 0,-1,  0, 0,-1,  0, 0,-1,  0, 0,-1,
    0, 1, 0,  0, 1, 0,  0, 1, 0,  0, 1, 0,
    0,-1, 0,  0,-1, 0,  0,-1, 0,  0,-1, 0,
    1, 0, 0,  1, 0, 0,  1, 0, 0,  1, 0, 0,
   -1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0,
  ]);
  const indices = new Uint16Array([
     0,  1,  2,   0,  2,  3,
     4,  5,  6,   4,  6,  7,
     8,  9, 10,   8, 10, 11,
    12, 13, 14,  12, 14, 15,
    16, 17, 18,  16, 18, 19,
    20, 21, 22,  20, 22, 23,
  ]);
  return uploadGeometry(gl, positions, normals, indices);
}

function createSphereGeometry(gl, radius) {
  const slices = 24, stacks = 16;
  const positions = [], normals = [], indices = [];
  for (let s = 0; s <= stacks; s++) {
    const phi = (s / stacks) * Math.PI;
    const sinP = Math.sin(phi), cosP = Math.cos(phi);
    for (let l = 0; l <= slices; l++) {
      const theta = (l / slices) * 2 * Math.PI;
      const sinT = Math.sin(theta), cosT = Math.cos(theta);
      const nx = cosT * sinP, ny = cosP, nz = sinT * sinP;
      positions.push(radius * nx, radius * ny, radius * nz);
      normals.push(nx, ny, nz);
    }
  }
  for (let s = 0; s < stacks; s++) {
    for (let l = 0; l < slices; l++) {
      const a = s * (slices + 1) + l;
      const b = a + slices + 1;
      indices.push(a, b, a + 1, b, b + 1, a + 1);
    }
  }
  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

function createPlaneGeometry(gl, size) {
  const hw = size.x * 0.5, hh = size.y * 0.5;
  const positions = new Float32Array([-hw, 0, -hh, hw, 0, -hh, hw, 0, hh, -hw, 0, hh]);
  const normals = new Float32Array([0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0]);
  const indices = new Uint16Array([0, 1, 2, 0, 2, 3]);
  return uploadGeometry(gl, positions, normals, indices);
}

function createCylinderGeometry(gl, radius, height) {
  const segments = 24;
  const positions = [], normals = [], indices = [];
  const hh = height * 0.5;
  for (let i = 0; i <= segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    const cosT = Math.cos(theta), sinT = Math.sin(theta);
    positions.push(radius * cosT, hh, radius * sinT);
    normals.push(cosT, 0, sinT);
    positions.push(radius * cosT, -hh, radius * sinT);
    normals.push(cosT, 0, sinT);
  }
  for (let i = 0; i < segments; i++) {
    const a = i * 2, b = a + 1, c = a + 2, d = a + 3;
    indices.push(a, b, c, b, d, c);
  }
  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

function uploadGeometry(gl, positions, normals, indices, uvs) {
  const vao = gl.createVertexArray();
  gl.bindVertexArray(vao);
  const posBuf = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, posBuf);
  gl.bufferData(gl.ARRAY_BUFFER, positions, gl.STATIC_DRAW);
  gl.enableVertexAttribArray(0);
  gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);
  const normBuf = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, normBuf);
  gl.bufferData(gl.ARRAY_BUFFER, normals, gl.STATIC_DRAW);
  gl.enableVertexAttribArray(1);
  gl.vertexAttribPointer(1, 3, gl.FLOAT, false, 0, 0);
  if (uvs) {
    const uvBuf = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, uvBuf);
    gl.bufferData(gl.ARRAY_BUFFER, uvs, gl.STATIC_DRAW);
    gl.enableVertexAttribArray(2);
    gl.vertexAttribPointer(2, 2, gl.FLOAT, false, 0, 0);
  }
  const idxBuf = gl.createBuffer();
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, idxBuf);
  gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, indices, gl.STATIC_DRAW);
  gl.bindVertexArray(null);
  return { vao, count: indices.length };
}

/**
 * Create a textured quad (for icon nodes). Has UVs.
 */
function createQuadGeometry(gl, size) {
  const hw = size.x * 0.5, hh = size.y * 0.5;
  const positions = new Float32Array([-hw, -hh, 0, hw, -hh, 0, hw, hh, 0, -hw, hh, 0]);
  const normals = new Float32Array([0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1]);
  const uvs = new Float32Array([0, 1, 1, 1, 1, 0, 0, 0]);
  const indices = new Uint16Array([0, 1, 2, 0, 2, 3]);
  return uploadGeometry(gl, positions, normals, indices, uvs);
}

// ---------------------------------------------------------------------------
// Texture cache — loads images asynchronously, creates GL textures
// ---------------------------------------------------------------------------

function createTextureCache(gl, scheduleFrame) {
  const cache = new Map();
  // 1x1 white fallback while loading
  const fallbackTex = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, fallbackTex);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, 1, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE, new Uint8Array([255, 255, 255, 255]));

  function getTexture(url) {
    if (cache.has(url)) return cache.get(url);
    // Start loading
    const entry = { tex: fallbackTex, loaded: false };
    cache.set(url, entry);
    const img = new Image();
    img.crossOrigin = 'anonymous';
    img.onload = () => {
      const tex = gl.createTexture();
      gl.bindTexture(gl.TEXTURE_2D, tex);
      gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, img);
      gl.generateMipmap(gl.TEXTURE_2D);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
      entry.tex = tex;
      entry.loaded = true;
      scheduleFrame();  // re-render with loaded texture
    };
    img.onerror = () => console.warn('[reactive-gl] Failed to load texture:', url);
    img.src = url;
    return entry;
  }

  return { getTexture };
}

// ---------------------------------------------------------------------------
// Font atlas (canvas-based text rendering)
// ---------------------------------------------------------------------------

/**
 * Generate a font atlas by rendering glyphs to a 2D canvas.
 * Returns { texture, glyphs, lineHeight, atlasSize }.
 * Each glyph: { x, y, w, h, advance, xOff, yOff } in atlas pixel coords.
 */
function createFontAtlas(gl, fontFamily, fontSize) {
  const atlasSize = 512;
  const canvas2d = document.createElement('canvas');
  canvas2d.width = atlasSize;
  canvas2d.height = atlasSize;
  const ctx = canvas2d.getContext('2d');

  // Font setup — render at high resolution for quality
  const renderSize = Math.max(48, fontSize);
  ctx.font = `${renderSize}px ${fontFamily}`;
  ctx.textBaseline = 'top';
  ctx.fillStyle = 'white';

  // ASCII range 32-126 + some useful Unicode
  const chars = [];
  for (let i = 32; i <= 126; i++) chars.push(String.fromCharCode(i));
  // Add a few common Unicode chars
  for (const c of '…—–·×÷±≤≥≠∞°') chars.push(c);

  const padding = 2;
  let curX = padding, curY = padding;
  let rowHeight = 0;
  const glyphs = new Map();

  // Measure line height
  const metrics = ctx.measureText('M');
  const lineHeight = metrics.actualBoundingBoxDescent !== undefined
    ? (metrics.actualBoundingBoxAscent + metrics.actualBoundingBoxDescent)
    : renderSize;

  for (const ch of chars) {
    const m = ctx.measureText(ch);
    const w = Math.ceil(m.width) + padding * 2;
    const h = Math.ceil(lineHeight) + padding * 2;

    if (curX + w > atlasSize) {
      curX = padding;
      curY += rowHeight + padding;
      rowHeight = 0;
    }
    if (curY + h > atlasSize) break; // atlas full

    ctx.fillText(ch, curX + padding, curY + padding);
    glyphs.set(ch, {
      x: curX, y: curY,
      w, h,
      advance: m.width / renderSize, // normalized to unit size
      xOff: 0, yOff: 0,
    });

    curX += w + padding;
    rowHeight = Math.max(rowHeight, h);
  }

  // Upload to WebGL texture
  const tex = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, tex);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, canvas2d);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);

  return { texture: tex, glyphs, lineHeight: lineHeight / renderSize, atlasSize, renderSize };
}

/**
 * Font atlas cache — one atlas per font family.
 */
function createFontCache(gl) {
  const cache = new Map();

  function getAtlas(fontRef) {
    const key = fontRef.type === 'builtin'
      ? `builtin:${fontRef.name}`
      : `custom:${fontRef.url}`;

    if (cache.has(key)) return cache.get(key);

    const family = fontRef.type === 'builtin'
      ? (fontRef.name === 'mono' ? 'monospace' : 'sans-serif')
      : fontRef.url; // custom font: user provides CSS font-family or loads via @font-face

    const atlas = createFontAtlas(gl, family, 48);
    cache.set(key, atlas);
    return atlas;
  }

  return { getAtlas };
}

/**
 * Build text geometry: a quad per glyph with positions and UVs.
 * Returns { positions: Float32Array, uvs: Float32Array, indices: Uint16Array, count, width, height }.
 * Text is laid out in the XY plane, centered at origin based on alignment.
 * Scale: 1 unit = textStyle.size world units.
 */
function buildTextGeometry(text, style, fontAtlas) {
  if (!text || text.length === 0) {
    return { positions: new Float32Array(0), uvs: new Float32Array(0), indices: new Uint16Array(0), count: 0, width: 0, height: 0 };
  }

  const { glyphs, lineHeight, atlasSize } = fontAtlas;
  const positions = [];
  const uvs = [];
  const indices = [];

  // Layout: compute lines first
  const lines = [];
  let currentLine = [];
  let lineWidth = 0;
  const maxWidth = style.layout.type === 'singleLine' ? Infinity
    : (style.layout.maxWidth / style.size); // convert to normalized units

  for (let i = 0; i < text.length; i++) {
    const ch = text[i];
    if (ch === '\n') {
      lines.push({ chars: currentLine, width: lineWidth });
      currentLine = [];
      lineWidth = 0;
      continue;
    }

    const g = glyphs.get(ch) || glyphs.get('?') || glyphs.get(' ');
    if (!g) continue;

    // Word wrap
    if (style.layout.type === 'wrapAt' && lineWidth + g.advance > maxWidth && currentLine.length > 0) {
      lines.push({ chars: currentLine, width: lineWidth });
      currentLine = [];
      lineWidth = 0;
    }

    // Ellipsis
    if (style.layout.type === 'ellipsis' && lineWidth + g.advance > maxWidth) {
      // Replace last char with '…'
      const ellipG = glyphs.get('…') || glyphs.get('.');
      if (ellipG && currentLine.length > 0) {
        currentLine[currentLine.length - 1] = { ch: '…', glyph: ellipG };
        lineWidth = currentLine.reduce((sum, c) => sum + c.glyph.advance, 0);
      }
      lines.push({ chars: currentLine, width: lineWidth });
      currentLine = null; // stop processing
      break;
    }

    currentLine.push({ ch, glyph: g });
    lineWidth += g.advance;
  }
  if (currentLine) {
    lines.push({ chars: currentLine, width: lineWidth });
  }

  // Total height
  const totalHeight = lines.length * lineHeight;
  let vertIdx = 0;

  for (let li = 0; li < lines.length; li++) {
    const line = lines[li];
    // X offset for alignment
    let xOff = 0;
    if (style.align === 'center') xOff = -line.width * 0.5;
    else if (style.align === 'right') xOff = -line.width;
    // Y position: top-down, centered vertically
    const yBase = (totalHeight * 0.5) - li * lineHeight;

    let cx = xOff;
    for (const { glyph } of line.chars) {
      const gw = glyph.advance;
      const gh = lineHeight;

      // Quad corners (in XY plane, Z=0)
      // Bottom-left, bottom-right, top-right, top-left
      const x0 = cx, x1 = cx + gw;
      const y0 = yBase - gh, y1 = yBase;

      positions.push(
        x0, y0, 0,
        x1, y0, 0,
        x1, y1, 0,
        x0, y1, 0
      );

      // UV coordinates from atlas
      const u0 = glyph.x / atlasSize;
      const v0 = (glyph.y + glyph.h) / atlasSize; // flip V (atlas is top-down, GL is bottom-up)
      const u1 = (glyph.x + glyph.w) / atlasSize;
      const v1 = glyph.y / atlasSize;

      uvs.push(
        u0, v0,
        u1, v0,
        u1, v1,
        u0, v1
      );

      // Two triangles per quad
      indices.push(
        vertIdx, vertIdx + 1, vertIdx + 2,
        vertIdx, vertIdx + 2, vertIdx + 3
      );
      vertIdx += 4;
      cx += gw;
    }
  }

  return {
    positions: new Float32Array(positions),
    uvs: new Float32Array(uvs),
    indices: new Uint16Array(indices),
    count: indices.length,
    width: Math.max(...lines.map(l => l.width)),
    height: totalHeight,
  };
}

/**
 * Create a WebGL VAO for text geometry.
 */
function createTextVAO(gl, textGeo) {
  if (textGeo.count === 0) return { vao: null, count: 0 };

  const vao = gl.createVertexArray();
  gl.bindVertexArray(vao);

  // Positions (attribute 0)
  const posBuf = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, posBuf);
  gl.bufferData(gl.ARRAY_BUFFER, textGeo.positions, gl.STATIC_DRAW);
  gl.enableVertexAttribArray(0);
  gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);

  // Normals (attribute 1) — dummy normals for text (facing +Z)
  const normalData = new Float32Array(textGeo.positions.length);
  for (let i = 0; i < normalData.length; i += 3) {
    normalData[i] = 0; normalData[i + 1] = 0; normalData[i + 2] = 1;
  }
  const normBuf = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, normBuf);
  gl.bufferData(gl.ARRAY_BUFFER, normalData, gl.STATIC_DRAW);
  gl.enableVertexAttribArray(1);
  gl.vertexAttribPointer(1, 3, gl.FLOAT, false, 0, 0);

  // UVs (attribute 2)
  const uvBuf = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, uvBuf);
  gl.bufferData(gl.ARRAY_BUFFER, textGeo.uvs, gl.STATIC_DRAW);
  gl.enableVertexAttribArray(2);
  gl.vertexAttribPointer(2, 2, gl.FLOAT, false, 0, 0);

  // Index buffer
  const idxBuf = gl.createBuffer();
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, idxBuf);
  gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, textGeo.indices, gl.STATIC_DRAW);

  gl.bindVertexArray(null);

  return { vao, count: textGeo.count, posBuf, uvBuf, normBuf, idxBuf };
}

/**
 * Update an existing text VAO with new geometry (for bindText3D).
 */
function updateTextVAO(gl, vaoEntry, textGeo) {
  if (textGeo.count === 0) {
    vaoEntry.count = 0;
    return;
  }
  if (!vaoEntry.vao) {
    // Need to create fresh
    Object.assign(vaoEntry, createTextVAO(gl, textGeo));
    return;
  }

  gl.bindVertexArray(vaoEntry.vao);

  gl.bindBuffer(gl.ARRAY_BUFFER, vaoEntry.posBuf);
  gl.bufferData(gl.ARRAY_BUFFER, textGeo.positions, gl.DYNAMIC_DRAW);

  gl.bindBuffer(gl.ARRAY_BUFFER, vaoEntry.uvBuf);
  gl.bufferData(gl.ARRAY_BUFFER, textGeo.uvs, gl.DYNAMIC_DRAW);

  // Update normals
  const normalData = new Float32Array(textGeo.positions.length);
  for (let i = 0; i < normalData.length; i += 3) {
    normalData[i] = 0; normalData[i + 1] = 0; normalData[i + 2] = 1;
  }
  gl.bindBuffer(gl.ARRAY_BUFFER, vaoEntry.normBuf);
  gl.bufferData(gl.ARRAY_BUFFER, normalData, gl.DYNAMIC_DRAW);

  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, vaoEntry.idxBuf);
  gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, textGeo.indices, gl.DYNAMIC_DRAW);

  gl.bindVertexArray(null);
  vaoEntry.count = textGeo.count;
}

// ---------------------------------------------------------------------------
// Text shader (alpha-tested texture rendering for font atlas)
// ---------------------------------------------------------------------------

const TEXT_VERT_SRC = `#version 300 es
precision highp float;
layout(location=0) in vec3 a_position;
layout(location=2) in vec2 a_uv;
uniform mat4 u_model;
uniform mat4 u_view;
uniform mat4 u_proj;
out vec2 v_uv;
void main() {
  v_uv = a_uv;
  gl_Position = u_proj * u_view * u_model * vec4(a_position, 1.0);
}
`;

const TEXT_FRAG_SRC = `#version 300 es
precision highp float;
in vec2 v_uv;
uniform sampler2D u_atlas;
uniform vec4 u_color;
out vec4 fragColor;
void main() {
  float alpha = texture(u_atlas, v_uv).r;
  if (alpha < 0.1) discard;
  fragColor = vec4(u_color.rgb, u_color.a * alpha);
}
`;

function createTextRenderProgram(gl) {
  const vert = compileShader(gl, gl.VERTEX_SHADER, TEXT_VERT_SRC);
  const frag = compileShader(gl, gl.FRAGMENT_SHADER, TEXT_FRAG_SRC);
  const prog = gl.createProgram();
  gl.attachShader(prog, vert);
  gl.attachShader(prog, frag);
  gl.linkProgram(prog);
  if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
    throw new Error('Text program link error: ' + gl.getProgramInfoLog(prog));
  }
  return {
    program: prog,
    uniforms: {
      model: gl.getUniformLocation(prog, 'u_model'),
      view:  gl.getUniformLocation(prog, 'u_view'),
      proj:  gl.getUniformLocation(prog, 'u_proj'),
      color: gl.getUniformLocation(prog, 'u_color'),
      atlas: gl.getUniformLocation(prog, 'u_atlas'),
    }
  };
}

// ---------------------------------------------------------------------------
// Shader compilation
// ---------------------------------------------------------------------------

function compileShader(gl, type, source) {
  const shader = gl.createShader(type);
  gl.shaderSource(shader, source);
  gl.compileShader(shader);
  if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
    const log = gl.getShaderInfoLog(shader);
    gl.deleteShader(shader);
    throw new Error('Shader compile error: ' + log);
  }
  return shader;
}

function createProgram(gl) {
  const vert = compileShader(gl, gl.VERTEX_SHADER, VERT_SRC);
  const frag = compileShader(gl, gl.FRAGMENT_SHADER, FRAG_SRC);
  const prog = gl.createProgram();
  gl.attachShader(prog, vert);
  gl.attachShader(prog, frag);
  gl.linkProgram(prog);
  if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
    const log = gl.getProgramInfoLog(prog);
    gl.deleteProgram(prog);
    throw new Error('Program link error: ' + log);
  }
  return {
    program: prog,
    uniforms: {
      model: gl.getUniformLocation(prog, 'u_model'),
      view:  gl.getUniformLocation(prog, 'u_view'),
      proj:  gl.getUniformLocation(prog, 'u_proj'),
      color: gl.getUniformLocation(prog, 'u_color'),
    }
  };
}

function createPhongProgram(gl) {
  const vert = compileShader(gl, gl.VERTEX_SHADER, PHONG_VERT_SRC);
  const frag = compileShader(gl, gl.FRAGMENT_SHADER, PHONG_FRAG_SRC);
  const prog = gl.createProgram();
  gl.attachShader(prog, vert);
  gl.attachShader(prog, frag);
  gl.linkProgram(prog);
  if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
    const log = gl.getProgramInfoLog(prog);
    gl.deleteProgram(prog);
    throw new Error('Phong program link error: ' + log);
  }
  const uniforms = {
    model:     gl.getUniformLocation(prog, 'u_model'),
    view:      gl.getUniformLocation(prog, 'u_view'),
    proj:      gl.getUniformLocation(prog, 'u_proj'),
    color:     gl.getUniformLocation(prog, 'u_color'),
    shininess: gl.getUniformLocation(prog, 'u_shininess'),
    cameraPos: gl.getUniformLocation(prog, 'u_cameraPos'),
    flatMode:  gl.getUniformLocation(prog, 'u_flatMode'),
    numLights: gl.getUniformLocation(prog, 'u_numLights'),
    lightType: [],
    lightColor: [],
    lightIntensity: [],
    lightDir: [],
    lightPos: [],
    lightRange: [],
    lightAngle: [],
    lightFalloff: [],
  };
  for (let i = 0; i < 8; i++) {
    uniforms.lightType.push(gl.getUniformLocation(prog, `u_lightType[${i}]`));
    uniforms.lightColor.push(gl.getUniformLocation(prog, `u_lightColor[${i}]`));
    uniforms.lightIntensity.push(gl.getUniformLocation(prog, `u_lightIntensity[${i}]`));
    uniforms.lightDir.push(gl.getUniformLocation(prog, `u_lightDir[${i}]`));
    uniforms.lightPos.push(gl.getUniformLocation(prog, `u_lightPos[${i}]`));
    uniforms.lightRange.push(gl.getUniformLocation(prog, `u_lightRange[${i}]`));
    uniforms.lightAngle.push(gl.getUniformLocation(prog, `u_lightAngle[${i}]`));
    uniforms.lightFalloff.push(gl.getUniformLocation(prog, `u_lightFalloff[${i}]`));
  }
  return { program: prog, uniforms };
}

function createPbrProgram(gl) {
  const vert = compileShader(gl, gl.VERTEX_SHADER, PBR_VERT_SRC);
  const frag = compileShader(gl, gl.FRAGMENT_SHADER, PBR_FRAG_SRC);
  const prog = gl.createProgram();
  gl.attachShader(prog, vert);
  gl.attachShader(prog, frag);
  gl.linkProgram(prog);
  if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
    const log = gl.getProgramInfoLog(prog);
    gl.deleteProgram(prog);
    throw new Error('PBR program link error: ' + log);
  }
  const uniforms = {
    model:     gl.getUniformLocation(prog, 'u_model'),
    view:      gl.getUniformLocation(prog, 'u_view'),
    proj:      gl.getUniformLocation(prog, 'u_proj'),
    color:     gl.getUniformLocation(prog, 'u_color'),
    metallic:  gl.getUniformLocation(prog, 'u_metallic'),
    roughness: gl.getUniformLocation(prog, 'u_roughness'),
    cameraPos: gl.getUniformLocation(prog, 'u_cameraPos'),
    numLights: gl.getUniformLocation(prog, 'u_numLights'),
    lightType: [], lightColor: [], lightIntensity: [],
    lightDir: [], lightPos: [], lightRange: [],
    lightAngle: [], lightFalloff: [],
  };
  for (let i = 0; i < 8; i++) {
    uniforms.lightType.push(gl.getUniformLocation(prog, `u_lightType[${i}]`));
    uniforms.lightColor.push(gl.getUniformLocation(prog, `u_lightColor[${i}]`));
    uniforms.lightIntensity.push(gl.getUniformLocation(prog, `u_lightIntensity[${i}]`));
    uniforms.lightDir.push(gl.getUniformLocation(prog, `u_lightDir[${i}]`));
    uniforms.lightPos.push(gl.getUniformLocation(prog, `u_lightPos[${i}]`));
    uniforms.lightRange.push(gl.getUniformLocation(prog, `u_lightRange[${i}]`));
    uniforms.lightAngle.push(gl.getUniformLocation(prog, `u_lightAngle[${i}]`));
    uniforms.lightFalloff.push(gl.getUniformLocation(prog, `u_lightFalloff[${i}]`));
  }
  return { program: prog, uniforms };
}

function createTexProgram(gl) {
  const vert = compileShader(gl, gl.VERTEX_SHADER, TEX_VERT_SRC);
  const frag = compileShader(gl, gl.FRAGMENT_SHADER, TEX_FRAG_SRC);
  const prog = gl.createProgram();
  gl.attachShader(prog, vert);
  gl.attachShader(prog, frag);
  gl.linkProgram(prog);
  if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
    const log = gl.getProgramInfoLog(prog);
    gl.deleteProgram(prog);
    throw new Error('Tex program link error: ' + log);
  }
  return {
    program: prog,
    uniforms: {
      model:   gl.getUniformLocation(prog, 'u_model'),
      view:    gl.getUniformLocation(prog, 'u_view'),
      proj:    gl.getUniformLocation(prog, 'u_proj'),
      color:   gl.getUniformLocation(prog, 'u_color'),
      texture: gl.getUniformLocation(prog, 'u_texture'),
    }
  };
}

function createPickProgram(gl) {
  const vert = compileShader(gl, gl.VERTEX_SHADER, PICK_VERT_SRC);
  const frag = compileShader(gl, gl.FRAGMENT_SHADER, PICK_FRAG_SRC);
  const prog = gl.createProgram();
  gl.attachShader(prog, vert);
  gl.attachShader(prog, frag);
  gl.linkProgram(prog);
  if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
    const log = gl.getProgramInfoLog(prog);
    gl.deleteProgram(prog);
    throw new Error('Pick program link error: ' + log);
  }
  return {
    program: prog,
    uniforms: {
      model:    gl.getUniformLocation(prog, 'u_model'),
      view:     gl.getUniformLocation(prog, 'u_view'),
      proj:     gl.getUniformLocation(prog, 'u_proj'),
      objectId: gl.getUniformLocation(prog, 'u_objectId'),
    }
  };
}

/**
 * Create offscreen framebuffer for color picking.
 * Renders at full canvas resolution with RGBA8 color + depth.
 */
function createPickFramebuffer(gl, width, height) {
  const fb = gl.createFramebuffer();
  gl.bindFramebuffer(gl.FRAMEBUFFER, fb);

  const colorTex = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, colorTex);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, width, height, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, colorTex, 0);

  const depthRb = gl.createRenderbuffer();
  gl.bindRenderbuffer(gl.RENDERBUFFER, depthRb);
  gl.renderbufferStorage(gl.RENDERBUFFER, gl.DEPTH_COMPONENT24, width, height);
  gl.framebufferRenderbuffer(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.RENDERBUFFER, depthRb);

  gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  return { fb, colorTex, depthRb, width, height };
}

// ---------------------------------------------------------------------------
// Geometry cache
// ---------------------------------------------------------------------------

function geometryKey(geom) {
  switch (geom.type) {
    case 'box':      return `box:${geom.dims.x},${geom.dims.y},${geom.dims.z}`;
    case 'sphere':   return `sphere:${geom.radius}`;
    case 'plane':    return `plane:${geom.size.x},${geom.size.y}`;
    case 'cylinder': return `cylinder:${geom.radius},${geom.height}`;
    case 'quad':     return `quad:${geom.size.x},${geom.size.y}`;
    case 'custom':   return null;  // custom geometry not cacheable
    default:         return null;
  }
}

function getOrCreateGeometry(gl, cache, geom) {
  const key = geometryKey(geom);
  if (key && cache.has(key)) return cache.get(key);
  let result;
  switch (geom.type) {
    case 'box':      result = createBoxGeometry(gl, geom.dims); break;
    case 'sphere':   result = createSphereGeometry(gl, geom.radius); break;
    case 'plane':    result = createPlaneGeometry(gl, geom.size); break;
    case 'cylinder': result = createCylinderGeometry(gl, geom.radius, geom.height); break;
    case 'quad':     result = createQuadGeometry(gl, geom.size); break;
    case 'custom':   result = geom.handle; break;  // handle IS the {vao, count} object
    default: throw new Error('Unknown geometry type: ' + geom.type);
  }
  if (key) cache.set(key, result);
  return result;
}

// ---------------------------------------------------------------------------
// Easing functions — map [0,1] → [0,1]
// ---------------------------------------------------------------------------

const easingFunctions = {
  linear:    (t) => t,
  easeIn:    (t) => t * t,
  easeOut:   (t) => 1 - (1 - t) * (1 - t),
  easeInOut: (t) => t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) * (-2 * t + 2) / 2,
};

/**
 * Create a cubic-bezier easing function (CSS-style).
 * Solves for t given x using Newton's method, then evaluates y(t).
 */
function makeCubicBezier(x1, y1, x2, y2) {
  // Bernstein polynomial coefficients for x(t) and y(t)
  const cx = 3 * x1, bx = 3 * (x2 - x1) - cx, ax = 1 - cx - bx;
  const cy = 3 * y1, by = 3 * (y2 - y1) - cy, ay = 1 - cy - by;

  function sampleX(t) { return ((ax * t + bx) * t + cx) * t; }
  function sampleY(t) { return ((ay * t + by) * t + cy) * t; }
  function sampleDerivX(t) { return (3 * ax * t + 2 * bx) * t + cx; }

  function solveT(x) {
    // Newton-Raphson
    let t = x;
    for (let i = 0; i < 8; i++) {
      const err = sampleX(t) - x;
      if (Math.abs(err) < 1e-7) return t;
      const d = sampleDerivX(t);
      if (Math.abs(d) < 1e-7) break;
      t -= err / d;
    }
    // Bisection fallback
    let lo = 0, hi = 1;
    t = x;
    for (let i = 0; i < 20; i++) {
      const v = sampleX(t);
      if (Math.abs(v - x) < 1e-7) return t;
      if (v < x) lo = t; else hi = t;
      t = (lo + hi) * 0.5;
    }
    return t;
  }

  return (x) => {
    if (x <= 0) return 0;
    if (x >= 1) return 1;
    return sampleY(solveT(x));
  };
}

/**
 * Resolve an easing spec (string or cubicBezier object) to a function.
 */
function resolveEasing(easing) {
  if (typeof easing === 'string') return easingFunctions[easing] || easingFunctions.linear;
  if (easing && easing.type === 'cubicBezier') return makeCubicBezier(easing.x1, easing.y1, easing.x2, easing.y2);
  return easingFunctions.linear;
}

// ---------------------------------------------------------------------------
// Interpolation — lerp / slerp for transforms and materials
// ---------------------------------------------------------------------------

function lerpFloat(a, b, t) {
  return a + (b - a) * t;
}

function lerpVec3(a, b, t) {
  return {
    x: a.x + (b.x - a.x) * t,
    y: a.y + (b.y - a.y) * t,
    z: a.z + (b.z - a.z) * t,
  };
}

function lerpColor(a, b, t) {
  return {
    r: a.r + (b.r - a.r) * t,
    g: a.g + (b.g - a.g) * t,
    b: a.b + (b.b - a.b) * t,
    a: a.a + (b.a - a.a) * t,
  };
}

/**
 * Spherical linear interpolation for quaternions.
 */
function slerpQuat(a, b, t) {
  let dot = a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w;
  // If negative dot, negate one quat to take shortest path
  let bx = b.x, by = b.y, bz = b.z, bw = b.w;
  if (dot < 0) {
    dot = -dot;
    bx = -bx; by = -by; bz = -bz; bw = -bw;
  }
  let s0, s1;
  if (dot > 0.9995) {
    // Very close — use linear interpolation to avoid divide-by-zero
    s0 = 1 - t;
    s1 = t;
  } else {
    const theta = Math.acos(dot);
    const sinTheta = Math.sin(theta);
    s0 = Math.sin((1 - t) * theta) / sinTheta;
    s1 = Math.sin(t * theta) / sinTheta;
  }
  return {
    x: s0 * a.x + s1 * bx,
    y: s0 * a.y + s1 * by,
    z: s0 * a.z + s1 * bz,
    w: s0 * a.w + s1 * bw,
  };
}

/**
 * Interpolate two interpreted transforms.
 */
function lerpTransform(a, b, t) {
  return {
    pos:   lerpVec3(a.pos, b.pos, t),
    rot:   slerpQuat(a.rot, b.rot, t),
    scale: lerpVec3(a.scale, b.scale, t),
  };
}

/**
 * Interpolate two interpreted materials of the same type.
 * Returns the target if types differ (no interpolation possible).
 */
function lerpMaterial(a, b, t) {
  if (a.type !== b.type) return b;
  if (a.type === 'unlit') {
    return { type: 'unlit', color: lerpColor(a.color, b.color, t) };
  }
  if (a.type === 'flat') {
    return { type: 'flat', color: lerpColor(a.color, b.color, t) };
  }
  if (a.type === 'phong') {
    return {
      type: 'phong',
      color: lerpColor(a.color, b.color, t),
      shininess: lerpFloat(a.shininess, b.shininess, t),
    };
  }
  if (a.type === 'pbr') {
    return {
      type: 'pbr',
      color: lerpColor(a.color, b.color, t),
      metallic: lerpFloat(a.metallic, b.metallic, t),
      roughness: lerpFloat(a.roughness, b.roughness, t),
    };
  }
  return b;
}

/**
 * Extract transition spec from an attrs list (first transition attr found).
 * Returns { durationMs, easing } or null.
 */
function findTransition(attrs) {
  if (!attrs) return null;
  for (const a of attrs) {
    if (a.type === 'transition') return a;
  }
  return null;
}

// ---------------------------------------------------------------------------
// GL Bindings — reactive scene graph nodes
// ---------------------------------------------------------------------------

/**
 * Walk the interpreted scene tree, collect GL bindings and picking registry.
 * Each binding has:
 *   { extract, lastValue, apply, type }
 *
 * - extract: Scott-encoded function (Model → Scott-encoded value)
 * - lastValue: cached plain JS value from last model
 * - apply: function(newValue) that updates the render node in place
 * - type: 'transform' or 'material' (for debugging)
 *
 * pickRegistry: Map<id:number, { entry, attrs }> — interactive objects
 *
 * Also builds a flat render list for drawing.
 */
function collectBindings(nodes, model, bindings, pickRegistry, lights, animateNodes) {
  const renderList = [];

  for (const node of nodes) {
    collectNode(node, null, renderList, bindings, model, pickRegistry, lights, animateNodes);
  }

  return renderList;
}

/**
 * Encode a pick ID (1-based integer) as an RGB vec3 (0.0–1.0 per channel).
 * ID 0 means "background / no object".
 */
function pickIdToRGB(id) {
  const r = ((id >>  0) & 0xFF) / 255;
  const g = ((id >>  8) & 0xFF) / 255;
  const b = ((id >> 16) & 0xFF) / 255;
  return { r, g, b };
}

/**
 * Decode readPixels RGBA bytes back to a pick ID.
 */
function rgbToPickId(r, g, b) {
  return r | (g << 8) | (b << 16);
}

/**
 * Register a render entry with the pick registry if it has interactive attrs.
 * Assigns a unique pickId to the entry for color picking.
 */
function registerPickable(entry, attrs, pickRegistry) {
  if (attrs && attrs.length > 0) {
    const pickId = pickRegistry.nextId++;
    entry.pickId = pickId;
    pickRegistry.map.set(pickId, { entry, attrs });
  }
}

/**
 * Recursively process a render node.
 * overrideTransform: if a parent bindTransform provides a transform, pass it down.
 */
function collectNode(node, overrideTransform, renderList, bindings, model, pickRegistry, lights, animateNodes) {
  switch (node.type) {
    case 'mesh': {
      const entry = {
        type: 'mesh',
        geometry: node.geometry,
        material: node.material,
        transform: overrideTransform || node.transform,
      };
      registerPickable(entry, node.attrs, pickRegistry);
      renderList.push(entry);
      break;
    }

    case 'icon': {
      // Icon = textured quad mesh
      const entry = {
        type: 'mesh',
        geometry: { type: 'quad', size: node.size },
        material: { type: 'textured', url: node.url, tint: { r: 1, g: 1, b: 1, a: 1 } },
        transform: overrideTransform || node.transform,
      };
      registerPickable(entry, node.attrs, pickRegistry);
      renderList.push(entry);
      break;
    }

    case 'group': {
      const groupTransform = overrideTransform || node.transform;
      const children = [];
      for (const child of node.children) {
        collectNode(child, null, children, bindings, model, pickRegistry, lights, animateNodes);
      }
      renderList.push({
        type: 'group',
        transform: groupTransform,
        children,
      });
      break;
    }

    case 'light': {
      lights.push(node.light);
      break;
    }

    case 'bindLight': {
      const scottLight = node.extract(model);
      const initialLight = interpretLight(scottLight);
      const lightIndex = lights.length;
      lights.push(initialLight);

      bindings.push({
        type: 'light',
        extract: node.extract,
        lastValue: initialLight,
        lightIndex,
        lightsRef: lights,
      });
      break;
    }

    case 'animate': {
      // Evaluate the time function at t=0 for initial transform
      const scottTransform = node.timeFn(0.0);
      const initialTransform = interpretTransform(scottTransform);

      // Process child with initial transform
      const childEntries = [];
      collectNode(node.child, initialTransform, childEntries, bindings, model, pickRegistry, lights, animateNodes);

      // Register animate node: each frame, call timeFn(t) and update child entries
      animateNodes.push({
        timeFn: node.timeFn,
        targets: childEntries,
      });

      renderList.push(...childEntries);
      break;
    }

    case 'bindTransform': {
      // Extract initial transform from model
      const scottTransform = node.extract(model);
      const initialTransform = interpretTransform(scottTransform);

      // Create a mutable render entry from the child
      // The child could be a mesh, bindMaterial, group, etc.
      const childEntries = [];
      collectNode(node.child, initialTransform, childEntries, bindings, model, pickRegistry, lights, animateNodes);

      // Look for transition spec in child's attrs
      const childAttrs = node.child ? node.child.attrs : null;
      const trans = childAttrs ? findTransition(childAttrs) : null;

      // Register binding: on model change, re-extract and update all child entries
      bindings.push({
        type: 'transform',
        extract: node.extract,
        lastValue: initialTransform,
        targets: childEntries,  // entries whose transform we update
        // Transition animation state
        transition: trans,      // null or { durationMs, easing }
        animation: null,        // active animation: { from, to, startTime, durationMs, easingFn }
      });

      renderList.push(...childEntries);
      break;
    }

    case 'bindMaterial': {
      // Extract initial material from model
      const scottMat = node.extract(model);
      const initialMat = interpretMaterial(scottMat);

      const entry = {
        type: 'mesh',
        geometry: node.geometry,
        material: initialMat,
        transform: overrideTransform || node.transform,
      };
      registerPickable(entry, node.attrs, pickRegistry);

      // Look for transition spec in attrs
      const trans = findTransition(node.attrs);

      // Register binding
      bindings.push({
        type: 'material',
        extract: node.extract,
        lastValue: initialMat,
        target: entry,
        // Transition animation state
        transition: trans,
        animation: null,
      });

      renderList.push(entry);
      break;
    }

    case 'text3D': {
      const entry = {
        type: 'text',
        text: node.text,
        style: node.style,
        transform: overrideTransform || node.transform,
        // vao/count will be built lazily at render time
        textVAO: null,
      };
      registerPickable(entry, node.attrs, pickRegistry);
      renderList.push(entry);
      break;
    }

    case 'bindText3D': {
      // Extract initial text from model
      const initialText = node.extract(model);

      const entry = {
        type: 'text',
        text: initialText,
        style: node.style,
        transform: overrideTransform || node.transform,
        textVAO: null,
      };
      registerPickable(entry, node.attrs, pickRegistry);

      bindings.push({
        type: 'text',
        extract: node.extract,
        lastValue: initialText,
        target: entry,
      });

      renderList.push(entry);
      break;
    }
  }
}

/**
 * Compare two interpreted transforms for equality.
 */
function transformEqual(a, b) {
  return a.pos.x === b.pos.x && a.pos.y === b.pos.y && a.pos.z === b.pos.z
      && a.rot.x === b.rot.x && a.rot.y === b.rot.y && a.rot.z === b.rot.z && a.rot.w === b.rot.w
      && a.scale.x === b.scale.x && a.scale.y === b.scale.y && a.scale.z === b.scale.z;
}

/**
 * Compare two interpreted materials for equality.
 */
function materialEqual(a, b) {
  if (a.type !== b.type) return false;
  if (a.type === 'textured') {
    return a.url === b.url
      && a.tint.r === b.tint.r && a.tint.g === b.tint.g
      && a.tint.b === b.tint.b && a.tint.a === b.tint.a;
  }
  const colorEq = a.color.r === b.color.r && a.color.g === b.color.g
      && a.color.b === b.color.b && a.color.a === b.color.a;
  if (a.type === 'unlit' || a.type === 'flat') return colorEq;
  if (a.type === 'phong') return colorEq && a.shininess === b.shininess;
  if (a.type === 'pbr') return colorEq && a.metallic === b.metallic && a.roughness === b.roughness;
  return false;
}

/**
 * Update GL bindings on model change. Returns true if anything changed.
 * When a transition is present, starts an animation instead of snapping.
 */
function updateGLBindings(bindings, newModel, now) {
  let dirty = false;

  for (const b of bindings) {
    if (b.type === 'transform') {
      const scottVal = b.extract(newModel);
      const newVal = interpretTransform(scottVal);
      if (!transformEqual(b.lastValue, newVal)) {
        if (b.transition) {
          // Start animated transition from current displayed value to new target
          const currentValue = b.animation
            ? tickSingleAnimation(b, now).value  // mid-animation: start from current interpolated
            : b.lastValue;
          b.animation = {
            from: currentValue,
            to: newVal,
            startTime: now,
            durationMs: b.transition.durationMs,
            easingFn: resolveEasing(b.transition.easing),
          };
        } else {
          // Snap immediately
          for (const entry of b.targets) {
            entry.transform = newVal;
          }
        }
        b.lastValue = newVal;
        dirty = true;
      }
    } else if (b.type === 'material') {
      const scottVal = b.extract(newModel);
      const newVal = interpretMaterial(scottVal);
      if (!materialEqual(b.lastValue, newVal)) {
        if (b.transition) {
          const currentValue = b.animation
            ? tickSingleAnimation(b, now).value
            : b.lastValue;
          b.animation = {
            from: currentValue,
            to: newVal,
            startTime: now,
            durationMs: b.transition.durationMs,
            easingFn: resolveEasing(b.transition.easing),
          };
        } else {
          b.target.material = newVal;
        }
        b.lastValue = newVal;
        dirty = true;
      }
    } else if (b.type === 'light') {
      const scottVal = b.extract(newModel);
      const newVal = interpretLight(scottVal);
      // Simple comparison: always update (lights change rarely, cheap to re-upload)
      b.lightsRef[b.lightIndex] = newVal;
      b.lastValue = newVal;
      dirty = true;
    } else if (b.type === 'text') {
      const newText = b.extract(newModel);
      if (newText !== b.lastValue) {
        b.target.text = newText;
        b.target.textDirty = true; // rebuild VAO at next render
        b.lastValue = newText;
        dirty = true;
      }
    }
  }

  return dirty;
}

/**
 * Compute interpolated value for a single binding animation at time `now`.
 * Returns { value, done } where done=true means animation is complete.
 */
function tickSingleAnimation(binding, now) {
  const anim = binding.animation;
  const elapsed = now - anim.startTime;
  const rawT = Math.min(elapsed / anim.durationMs, 1.0);
  const t = anim.easingFn(rawT);
  const done = rawT >= 1.0;

  if (binding.type === 'transform') {
    return { value: lerpTransform(anim.from, anim.to, t), done };
  } else {
    return { value: lerpMaterial(anim.from, anim.to, t), done };
  }
}

/**
 * Tick all active animations. Apply interpolated values to render entries.
 * Returns number of still-active animations.
 */
function tickAnimations(bindings, now) {
  let activeCount = 0;

  for (const b of bindings) {
    if (!b.animation) continue;

    const { value, done } = tickSingleAnimation(b, now);

    if (b.type === 'transform') {
      for (const entry of b.targets) {
        entry.transform = value;
      }
    } else if (b.type === 'material') {
      b.target.material = value;
    }

    if (done) {
      b.animation = null;  // animation complete
    } else {
      activeCount++;
    }
  }

  return activeCount;
}

/**
 * Tick all animate nodes — call timeFn(t) and update child entry transforms.
 * t is in seconds (Float).
 */
function tickAnimateNodes(animateNodes, timeSeconds) {
  for (const anim of animateNodes) {
    const scottTransform = anim.timeFn(timeSeconds);
    const newTransform = interpretTransform(scottTransform);
    for (const entry of anim.targets) {
      entry.transform = newTransform;
    }
  }
}

// ---------------------------------------------------------------------------
// Scene renderer (draws from flat render list)
// ---------------------------------------------------------------------------

/**
 * Upload light uniforms to the phong program.
 */
function uploadLights(gl, phongProg, lights) {
  gl.uniform1i(phongProg.uniforms.numLights, Math.min(lights.length, 8));
  for (let i = 0; i < Math.min(lights.length, 8); i++) {
    const lt = lights[i];
    const c = lt.color;
    gl.uniform3f(phongProg.uniforms.lightColor[i], c.r, c.g, c.b);
    gl.uniform1f(phongProg.uniforms.lightIntensity[i], lt.intensity);
    if (lt.type === 'ambient') {
      gl.uniform1i(phongProg.uniforms.lightType[i], 0);
    } else if (lt.type === 'directional') {
      gl.uniform1i(phongProg.uniforms.lightType[i], 1);
      gl.uniform3f(phongProg.uniforms.lightDir[i], lt.direction.x, lt.direction.y, lt.direction.z);
    } else if (lt.type === 'point') {
      gl.uniform1i(phongProg.uniforms.lightType[i], 2);
      gl.uniform3f(phongProg.uniforms.lightPos[i], lt.position.x, lt.position.y, lt.position.z);
      gl.uniform1f(phongProg.uniforms.lightRange[i], lt.range);
    } else if (lt.type === 'spot') {
      gl.uniform1i(phongProg.uniforms.lightType[i], 3);
      gl.uniform3f(phongProg.uniforms.lightPos[i], lt.pos.x, lt.pos.y, lt.pos.z);
      gl.uniform3f(phongProg.uniforms.lightDir[i], lt.dir.x, lt.dir.y, lt.dir.z);
      gl.uniform1f(phongProg.uniforms.lightRange[i], lt.range || 100.0);
      gl.uniform1f(phongProg.uniforms.lightAngle[i], lt.angle);
      gl.uniform1f(phongProg.uniforms.lightFalloff[i], lt.falloff);
    }
  }
}

function renderEntry(gl, programs, geoCache, texCache, fontCache, entry, parentMat, lights, cameraPos) {
  if (entry.type === 'mesh') {
    const tfm = entry.transform;
    const modelMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);

    const mat = entry.material;
    const geo = getOrCreateGeometry(gl, geoCache, entry.geometry);

    if (mat.type === 'pbr' && lights.length > 0) {
      const prog = programs.pbr;
      const c = mat.color;
      gl.useProgram(prog.program);
      gl.uniformMatrix4fv(prog.uniforms.proj, false, programs._projMat);
      gl.uniformMatrix4fv(prog.uniforms.view, false, programs._viewMat);
      gl.uniformMatrix4fv(prog.uniforms.model, false, modelMat);
      gl.uniform4f(prog.uniforms.color, c.r, c.g, c.b, c.a);
      gl.uniform1f(prog.uniforms.metallic, mat.metallic);
      gl.uniform1f(prog.uniforms.roughness, mat.roughness);
      gl.uniform3f(prog.uniforms.cameraPos, cameraPos.x, cameraPos.y, cameraPos.z);
      uploadLights(gl, prog, lights);
    } else if (mat.type === 'textured' && programs.tex) {
      // Textured material
      const prog = programs.tex;
      gl.useProgram(prog.program);
      gl.uniformMatrix4fv(prog.uniforms.proj, false, programs._projMat);
      gl.uniformMatrix4fv(prog.uniforms.view, false, programs._viewMat);
      gl.uniformMatrix4fv(prog.uniforms.model, false, modelMat);
      const t = mat.tint;
      gl.uniform4f(prog.uniforms.color, t.r, t.g, t.b, t.a);
      // Bind texture
      const texEntry = texCache ? texCache.getTexture(mat.url) : null;
      if (texEntry) {
        gl.activeTexture(gl.TEXTURE0);
        gl.bindTexture(gl.TEXTURE_2D, texEntry.tex);
        gl.uniform1i(prog.uniforms.texture, 0);
      }
    } else if ((mat.type === 'phong' || mat.type === 'flat') && lights.length > 0) {
      const prog = programs.phong;
      const c = mat.color;
      gl.useProgram(prog.program);
      gl.uniformMatrix4fv(prog.uniforms.proj, false, programs._projMat);
      gl.uniformMatrix4fv(prog.uniforms.view, false, programs._viewMat);
      gl.uniformMatrix4fv(prog.uniforms.model, false, modelMat);
      gl.uniform4f(prog.uniforms.color, c.r, c.g, c.b, c.a);
      gl.uniform1f(prog.uniforms.shininess, mat.type === 'flat' ? 1.0 : mat.shininess);
      gl.uniform3f(prog.uniforms.cameraPos, cameraPos.x, cameraPos.y, cameraPos.z);
      gl.uniform1i(prog.uniforms.flatMode, mat.type === 'flat' ? 1 : 0);
      uploadLights(gl, prog, lights);
    } else {
      const prog = programs.unlit;
      const c = mat.color || mat.tint || { r: 1, g: 1, b: 1, a: 1 };
      gl.useProgram(prog.program);
      gl.uniformMatrix4fv(prog.uniforms.proj, false, programs._projMat);
      gl.uniformMatrix4fv(prog.uniforms.view, false, programs._viewMat);
      gl.uniformMatrix4fv(prog.uniforms.model, false, modelMat);
      gl.uniform4f(prog.uniforms.color, c.r, c.g, c.b, c.a);
    }

    gl.bindVertexArray(geo.vao);
    gl.drawElements(gl.TRIANGLES, geo.count, gl.UNSIGNED_SHORT, 0);
    gl.bindVertexArray(null);

  } else if (entry.type === 'group') {
    const tfm = entry.transform;
    const groupMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);

    for (const child of entry.children) {
      renderEntry(gl, programs, geoCache, texCache, fontCache, child, groupMat, lights, cameraPos);
    }
  } else if (entry.type === 'text') {
    const tfm = entry.transform;
    const modelMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);

    // Build or rebuild text VAO lazily
    if (!entry.textVAO || entry.textDirty) {
      const atlas = fontCache.getAtlas(entry.style.font);
      const textGeo = buildTextGeometry(entry.text, entry.style, atlas);
      if (!entry.textVAO) {
        entry.textVAO = createTextVAO(gl, textGeo);
        entry._atlas = atlas;
      } else {
        updateTextVAO(gl, entry.textVAO, textGeo);
      }
      entry.textDirty = false;
    }

    if (entry.textVAO && entry.textVAO.vao && entry.textVAO.count > 0) {
      // Apply text size as an additional scale factor
      const sizeScale = entry.style.size;
      const sizeMat = mat4FromTRS(
        { x: 0, y: 0, z: 0 },
        { x: 0, y: 0, z: 0, w: 1 },
        { x: sizeScale, y: sizeScale, z: sizeScale }
      );
      const finalMat = mat4Multiply(modelMat, sizeMat);

      const prog = programs.text;
      const c = entry.style.color;
      gl.useProgram(prog.program);
      gl.uniformMatrix4fv(prog.uniforms.proj, false, programs._projMat);
      gl.uniformMatrix4fv(prog.uniforms.view, false, programs._viewMat);
      gl.uniformMatrix4fv(prog.uniforms.model, false, finalMat);
      gl.uniform4f(prog.uniforms.color, c.r, c.g, c.b, c.a);
      gl.activeTexture(gl.TEXTURE0);
      gl.bindTexture(gl.TEXTURE_2D, entry._atlas.texture);
      gl.uniform1i(prog.uniforms.atlas, 0);

      // Enable blending for text (alpha from atlas)
      gl.enable(gl.BLEND);
      gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);

      gl.bindVertexArray(entry.textVAO.vao);
      gl.drawElements(gl.TRIANGLES, entry.textVAO.count, gl.UNSIGNED_SHORT, 0);
      gl.bindVertexArray(null);

      gl.disable(gl.BLEND);
    }
  }
}

/**
 * Check if a render entry is transparent (material alpha < 1.0).
 */
function isTransparent(entry) {
  if (entry.type === 'mesh') {
    const mat = entry.material;
    if (mat.type === 'textured') return mat.tint.a < 1.0;
    return mat.color.a < 1.0;
  }
  if (entry.type === 'group') return entry.children.some(isTransparent);
  return false;
}

/**
 * Estimate distance from camera to entry (for back-to-front sorting).
 * Uses transform position relative to camera.
 */
function entryDepth(entry, cameraPos) {
  const p = entry.transform ? entry.transform.pos : { x: 0, y: 0, z: 0 };
  const dx = p.x - cameraPos.x, dy = p.y - cameraPos.y, dz = p.z - cameraPos.z;
  return dx * dx + dy * dy + dz * dz;
}

function renderScene(gl, programs, geoCache, texCache, fontCache, renderList, projMat, viewMat, lights, cameraPos) {
  gl.viewport(0, 0, gl.canvas.width, gl.canvas.height);
  gl.clearColor(0.1, 0.1, 0.1, 1.0);
  gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
  gl.enable(gl.DEPTH_TEST);

  // Store matrices for program switches during rendering
  programs._projMat = projMat;
  programs._viewMat = viewMat;

  // Separate opaque and transparent entries
  const opaque = [];
  const transparent = [];
  for (const entry of renderList) {
    // Text entries are always rendered with blending (in transparent pass)
    if (entry.type === 'text' || isTransparent(entry)) {
      transparent.push(entry);
    } else {
      opaque.push(entry);
    }
  }

  // Pass 1: Render opaque objects (z-write ON)
  gl.depthMask(true);
  gl.disable(gl.BLEND);
  for (const entry of opaque) {
    renderEntry(gl, programs, geoCache, texCache, fontCache, entry, null, lights, cameraPos);
  }

  // Pass 2: Render transparent objects back-to-front (z-write OFF, blend ON)
  if (transparent.length > 0) {
    transparent.sort((a, b) => entryDepth(b, cameraPos) - entryDepth(a, cameraPos));
    gl.depthMask(false);
    gl.enable(gl.BLEND);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
    for (const entry of transparent) {
      renderEntry(gl, programs, geoCache, texCache, fontCache, entry, null, lights, cameraPos);
    }
    gl.depthMask(true);
    gl.disable(gl.BLEND);
  }
}

// ---------------------------------------------------------------------------
// Pick-buffer rendering (color picking pass)
// ---------------------------------------------------------------------------

/**
 * Render a single entry into the pick buffer with its pickId color.
 */
function renderPickEntry(gl, pickProg, geoCache, entry, parentMat) {
  if (entry.type === 'mesh') {
    const tfm = entry.transform;
    const modelMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);

    // Only render objects that have a pickId
    if (entry.pickId != null) {
      const geo = getOrCreateGeometry(gl, geoCache, entry.geometry);
      const idColor = pickIdToRGB(entry.pickId);

      gl.uniformMatrix4fv(pickProg.uniforms.model, false, modelMat);
      gl.uniform3f(pickProg.uniforms.objectId, idColor.r, idColor.g, idColor.b);

      gl.bindVertexArray(geo.vao);
      gl.drawElements(gl.TRIANGLES, geo.count, gl.UNSIGNED_SHORT, 0);
      gl.bindVertexArray(null);
    }
  } else if (entry.type === 'group') {
    const tfm = entry.transform;
    const groupMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);

    for (const child of entry.children) {
      renderPickEntry(gl, pickProg, geoCache, child, groupMat);
    }
  } else if (entry.type === 'text' && entry.pickId != null) {
    // Text picking: render text quads with pick color
    if (entry.textVAO && entry.textVAO.vao && entry.textVAO.count > 0) {
      const tfm = entry.transform;
      const modelMat = parentMat
        ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
        : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);

      const sizeScale = entry.style.size;
      const sizeMat = mat4FromTRS(
        { x: 0, y: 0, z: 0 },
        { x: 0, y: 0, z: 0, w: 1 },
        { x: sizeScale, y: sizeScale, z: sizeScale }
      );
      const finalMat = mat4Multiply(modelMat, sizeMat);

      const idColor = pickIdToRGB(entry.pickId);
      gl.uniformMatrix4fv(pickProg.uniforms.model, false, finalMat);
      gl.uniform3f(pickProg.uniforms.objectId, idColor.r, idColor.g, idColor.b);

      gl.bindVertexArray(entry.textVAO.vao);
      gl.drawElements(gl.TRIANGLES, entry.textVAO.count, gl.UNSIGNED_SHORT, 0);
      gl.bindVertexArray(null);
    }
  }
}

/**
 * Render the pick buffer — all interactive objects with unique ID colors.
 */
function renderPickBuffer(gl, pickProg, pickFB, geoCache, renderList, projMat, viewMat) {
  gl.bindFramebuffer(gl.FRAMEBUFFER, pickFB.fb);
  gl.viewport(0, 0, pickFB.width, pickFB.height);
  gl.clearColor(0, 0, 0, 1);  // ID 0 = background
  gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
  gl.enable(gl.DEPTH_TEST);

  gl.useProgram(pickProg.program);
  gl.uniformMatrix4fv(pickProg.uniforms.proj, false, projMat);
  gl.uniformMatrix4fv(pickProg.uniforms.view, false, viewMat);

  for (const entry of renderList) {
    renderPickEntry(gl, pickProg, geoCache, entry, null);
  }

  gl.bindFramebuffer(gl.FRAMEBUFFER, null);
}

/**
 * Read the pick ID at canvas pixel (x, y).
 * y is in DOM coordinates (top-down); converted to GL bottom-up.
 */
function readPickId(gl, pickFB, x, y) {
  gl.bindFramebuffer(gl.FRAMEBUFFER, pickFB.fb);
  const pixel = new Uint8Array(4);
  const glY = pickFB.height - 1 - y;
  gl.readPixels(x, glY, 1, 1, gl.RGBA, gl.UNSIGNED_BYTE, pixel);
  gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  return rgbToPickId(pixel[0], pixel[1], pixel[2]);
}

// ---------------------------------------------------------------------------
// Camera helpers
// ---------------------------------------------------------------------------

function buildProjectionMatrix(proj, aspect) {
  if (proj.type === 'orthographic') {
    return mat4Ortho(proj.size, aspect, proj.near, proj.far);
  } else if (proj.type === 'perspective') {
    return mat4Perspective(proj.fov, aspect, proj.near, proj.far);
  }
  return mat4Identity();
}

function buildCameraMatrices(cameraData, aspect, model) {
  let projMat, viewMat, cameraPos;
  const up = { x: 0, y: 1, z: 0 };

  if (cameraData.type === 'fixed') {
    projMat = buildProjectionMatrix(cameraData.projection, aspect);
    viewMat = mat4LookAt(cameraData.pos, cameraData.target, up);
    cameraPos = cameraData.pos;
  } else if (cameraData.type === 'fromModel') {
    const scottProj = cameraData.projExtract(model);
    const proj = interpretProjection(scottProj);
    projMat = buildProjectionMatrix(proj, aspect);
    const pos = cameraData.posExtract(model);
    const target = cameraData.targetExtract(model);
    viewMat = mat4LookAt(pos, target, up);
    cameraPos = pos;
  } else {
    projMat = mat4Identity();
    viewMat = mat4Identity();
    cameraPos = { x: 0, y: 0, z: 0 };
  }

  return { projMat, viewMat, cameraPos };
}

// ---------------------------------------------------------------------------
// Canvas initialization
// ---------------------------------------------------------------------------

function initGLCanvas(canvas) {
  const scene = canvas.__glScene;
  if (!scene) return;

  const gl = canvas.getContext('webgl2', { antialias: true });
  if (!gl) {
    console.error('WebGL2 not supported');
    return;
  }

  const getModel = canvas.__glGetModel;
  const dispatch = canvas.__glDispatch;
  const model = getModel ? getModel() : null;

  // Interpret Scott-encoded scene
  const sceneData = interpretScene(scene);
  const cameraData = interpretCamera(sceneData.camera);
  const rawNodes = listToArray(sceneData.nodes).map(interpretSceneNode);

  // Compile shaders (unlit + phong + pbr + textured + picking)
  const programs = {
    unlit: createProgram(gl),
    phong: createPhongProgram(gl),
    pbr:   createPbrProgram(gl),
    tex:   createTexProgram(gl),
    text:  createTextRenderProgram(gl),
    _projMat: null,
    _viewMat: null,
  };
  const pickProg = createPickProgram(gl);
  const geoCache = new Map();
  const fontCache = createFontCache(gl);

  // Pick registry: map from pickId → { entry, attrs }
  const pickRegistry = { nextId: 1, map: new Map() };

  // Collect bindings, render list, lights, and animate nodes
  const glBindings = [];
  const lights = [];
  const animateNodes = [];
  const renderList = collectBindings(rawNodes, model, glBindings, pickRegistry, lights, animateNodes);
  const hasAnimations = animateNodes.length > 0;

  // Pick framebuffer (only if there are interactive objects)
  const hasPickables = pickRegistry.map.size > 0;
  let pickFB = null;
  if (hasPickables) {
    pickFB = createPickFramebuffer(gl, canvas.width, canvas.height);
  }

  // Camera matrices
  let aspect = canvas.width / canvas.height;
  let { projMat, viewMat, cameraPos } = buildCameraMatrices(cameraData, aspect, model);

  // Camera bindings for fromModel
  let cameraBindings = null;
  if (cameraData.type === 'fromModel') {
    cameraBindings = {
      lastPos: cameraData.posExtract(model),
      lastTarget: cameraData.targetExtract(model),
      lastProj: interpretProjection(cameraData.projExtract(model)),
    };
  }

  // Render loop state: IDLE | DIRTY | ANIMATING
  //   IDLE      — no rAF, waiting for changes
  //   DIRTY     — one rAF scheduled for a single re-render
  //   ANIMATING — rAF loop active (transitions in progress)
  let renderState = 'IDLE';
  let pickDirty = hasPickables;  // pick buffer needs initial render

  function scheduleFrame() {
    if (renderState === 'IDLE') {
      renderState = 'DIRTY';
      requestAnimationFrame(doFrame);
    }
    // If ANIMATING, rAF is already looping — no action needed
    // If DIRTY, rAF already scheduled — no action needed
  }

  // Texture cache (loads images, triggers re-render on load)
  const texCache = createTextureCache(gl, scheduleFrame);

  function doFrame(timestamp) {
    // Tick continuous animate nodes (time in seconds)
    if (hasAnimations) {
      tickAnimateNodes(animateNodes, timestamp / 1000.0);
    }

    // Tick declarative transition animations
    const activeTransitions = tickAnimations(glBindings, timestamp);

    // Render the scene
    renderScene(gl, programs, geoCache, texCache, fontCache, renderList, projMat, viewMat, lights, cameraPos);

    // Pick buffer: don't render every frame — only on demand (mouse events
    // check pickDirty and re-render before reading). But mark dirty when
    // objects are moving (animations or transitions).
    if (hasPickables && (hasAnimations || activeTransitions > 0)) {
      pickDirty = true;
    }
    if (pickFB && pickDirty && !(hasAnimations || activeTransitions > 0)) {
      // Only render pick buffer eagerly when settling (no active animations)
      renderPickBuffer(gl, pickProg, pickFB, geoCache, renderList, projMat, viewMat);
      pickDirty = false;
    }

    if (hasAnimations || activeTransitions > 0) {
      // Keep animating — continuous animate nodes always need rAF
      renderState = 'ANIMATING';
      requestAnimationFrame(doFrame);
    } else {
      renderState = 'IDLE';
      // Mark pick buffer dirty after transitions complete (objects may have moved)
      if (hasPickables) pickDirty = true;
    }
  }

  // Initial render
  renderScene(gl, programs, geoCache, texCache, fontCache, renderList, projMat, viewMat, lights, cameraPos);
  if (pickFB) {
    renderPickBuffer(gl, pickProg, pickFB, geoCache, renderList, projMat, viewMat);
    pickDirty = false;
  }

  // If there are continuous animations, start the rAF loop immediately
  if (hasAnimations) {
    renderState = 'ANIMATING';
    requestAnimationFrame(doFrame);
  }

  // --- Mouse event handling (color picking + ray casting) ---

  let hoveredId = 0;  // currently hovered pick ID (0 = none)
  let focusedId = 0;  // currently focused pick ID for keyboard events
  let dragState = null; // { pickId, startPoint: Vec3 } — active drag

  function ensurePickBuffer() {
    if (pickDirty && pickFB) {
      renderPickBuffer(gl, pickProg, pickFB, geoCache, renderList, projMat, viewMat);
      pickDirty = false;
    }
  }

  function getPickIdAt(event) {
    if (!pickFB) return 0;
    const rect = canvas.getBoundingClientRect();
    const cssX = event.clientX - rect.left;
    const cssY = event.clientY - rect.top;
    // Convert CSS coords to canvas pixel coords
    const x = Math.round(cssX * (canvas.width / rect.width));
    const y = Math.round(cssY * (canvas.height / rect.height));
    if (x < 0 || x >= canvas.width || y < 0 || y >= canvas.height) return 0;
    return readPickId(gl, pickFB, x, y);
  }

  function dispatchAttr(pickId, attrType) {
    if (!dispatch || pickId === 0) return;
    const entry = pickRegistry.map.get(pickId);
    if (!entry) return;
    for (const attr of entry.attrs) {
      if (attr.type === attrType) {
        dispatch(attr.msg);
      }
    }
  }

  /**
   * Get the ray-cast hit point for the entry under the cursor.
   * Returns Vec3 or null.
   */
  function getRayHitAt(event, pickId) {
    if (!pickId || pickId === 0) return null;
    const regEntry = pickRegistry.map.get(pickId);
    if (!regEntry) return null;
    const ray = screenToRay(event.clientX, event.clientY, canvas, projMat, viewMat);
    if (!ray) return null;
    const hit = rayIntersectEntry(ray, regEntry.entry, null);
    return hit ? hit.point : null;
  }

  /**
   * Check if a pick registry entry has an attribute of a given type.
   */
  function entryHasAttr(pickId, attrType) {
    if (!pickId || pickId === 0) return false;
    const entry = pickRegistry.map.get(pickId);
    if (!entry) return false;
    return entry.attrs.some(a => a.type === attrType);
  }

  if (hasPickables) {
    canvas.addEventListener('click', (e) => {
      ensurePickBuffer();
      const id = getPickIdAt(e);
      if (!dispatch || id === 0) return;
      const entry = pickRegistry.map.get(id);
      if (!entry) return;

      for (const attr of entry.attrs) {
        if (attr.type === 'onClick') {
          dispatch(attr.msg);
        } else if (attr.type === 'onClickAt') {
          const point = getRayHitAt(e, id);
          if (point) {
            // Call the Agda handler: (Vec3 → Msg)
            // Vec3 is a postulate compiled as { x, y, z }
            dispatch(attr.handler(point));
          }
        }
      }

      // Focus management: clicking a focusable object focuses it
      if (entryHasAttr(id, 'focusable')) {
        focusedId = id;
      }
    });

    canvas.addEventListener('mousedown', (e) => {
      ensurePickBuffer();
      const id = getPickIdAt(e);
      if (!dispatch || id === 0) return;
      const entry = pickRegistry.map.get(id);
      if (!entry) return;

      // Start drag if entry has onDrag
      for (const attr of entry.attrs) {
        if (attr.type === 'onDrag') {
          const point = getRayHitAt(e, id);
          if (point) {
            dragState = { pickId: id, startPoint: point };
            e.preventDefault();
          }
          break;
        }
      }
    });

    canvas.addEventListener('mousemove', (e) => {
      // Handle active drag
      if (dragState && dispatch) {
        const ray = screenToRay(e.clientX, e.clientY, canvas, projMat, viewMat);
        if (ray) {
          // Project current mouse position onto a plane at the drag start point's depth
          // Use the plane perpendicular to the camera view direction at startPoint
          const camDir = {
            x: dragState.startPoint.x - cameraPos.x,
            y: dragState.startPoint.y - cameraPos.y,
            z: dragState.startPoint.z - cameraPos.z,
          };
          const camDirLen = Math.hypot(camDir.x, camDir.y, camDir.z);
          if (camDirLen > 1e-10) {
            const n = { x: camDir.x / camDirLen, y: camDir.y / camDirLen, z: camDir.z / camDirLen };
            // Plane: dot(n, p - startPoint) = 0
            // Ray: origin + t * dir
            // t = dot(n, startPoint - origin) / dot(n, dir)
            const denom = n.x * ray.dir.x + n.y * ray.dir.y + n.z * ray.dir.z;
            if (Math.abs(denom) > 1e-10) {
              const dx = dragState.startPoint.x - ray.origin.x;
              const dy = dragState.startPoint.y - ray.origin.y;
              const dz = dragState.startPoint.z - ray.origin.z;
              const t = (n.x * dx + n.y * dy + n.z * dz) / denom;
              if (t >= 0) {
                const currentPoint = rayAt(ray, t);
                const entry = pickRegistry.map.get(dragState.pickId);
                if (entry) {
                  for (const attr of entry.attrs) {
                    if (attr.type === 'onDrag') {
                      // onDrag : (Vec3 → Vec3 → Msg) — start, current
                      dispatch(attr.handler(dragState.startPoint)(currentPoint));
                    }
                  }
                }
              }
            }
          }
        }
        return; // Don't process hover during drag
      }

      ensurePickBuffer();
      const id = getPickIdAt(e);
      if (id !== hoveredId) {
        // Leave old
        if (hoveredId !== 0) dispatchAttr(hoveredId, 'onLeave');
        // Enter new
        hoveredId = id;
        if (hoveredId !== 0) dispatchAttr(hoveredId, 'onHover');
      }
    });

    canvas.addEventListener('mouseup', () => {
      dragState = null;
    });

    canvas.addEventListener('mouseleave', () => {
      if (hoveredId !== 0) {
        dispatchAttr(hoveredId, 'onLeave');
        hoveredId = 0;
      }
      dragState = null;
    });

    canvas.addEventListener('wheel', (e) => {
      ensurePickBuffer();
      const id = getPickIdAt(e);
      if (!dispatch || id === 0) return;
      const entry = pickRegistry.map.get(id);
      if (!entry) return;
      for (const attr of entry.attrs) {
        if (attr.type === 'onScroll') {
          e.preventDefault();
          // deltaY normalized: positive = scroll down, negative = scroll up
          dispatch(attr.handler(e.deltaY));
        }
      }
    }, { passive: false });

    // --- Keyboard event handling (focusable + onKeyDown + onInput) ---

    // Make canvas focusable for keyboard events
    if (canvas.tabIndex < 0) {
      canvas.tabIndex = 0;
      canvas.style.outline = 'none'; // prevent default focus outline on canvas
    }

    canvas.addEventListener('keydown', (e) => {
      if (!dispatch || focusedId === 0) return;
      const entry = pickRegistry.map.get(focusedId);
      if (!entry) return;

      for (const attr of entry.attrs) {
        if (attr.type === 'onKeyDown') {
          // KeyEvent is a postulate — at runtime it's the DOM KeyboardEvent
          // keyEventKey = e => e.key, etc. — matches the FFI pragmas
          dispatch(attr.handler(e));
          e.preventDefault();
        } else if (attr.type === 'onInput' && e.key.length === 1) {
          // onInput : (String → Msg) — single character input
          dispatch(attr.handler(e.key));
          e.preventDefault();
        }
      }
    });
  }

  // Register model update callback
  canvas.__glUpdate = (oldModel, newModel) => {
    const now = performance.now();
    let dirty = false;

    // Update GL bindings (transform, material) — may start animations
    if (glBindings.length > 0) {
      dirty = updateGLBindings(glBindings, newModel, now);
    }

    // Update camera if fromModel
    if (cameraData.type === 'fromModel') {
      const newPos = cameraData.posExtract(newModel);
      const newTarget = cameraData.targetExtract(newModel);
      const newProj = interpretProjection(cameraData.projExtract(newModel));
      const posChanged = !cameraBindings
        || newPos.x !== cameraBindings.lastPos.x
        || newPos.y !== cameraBindings.lastPos.y
        || newPos.z !== cameraBindings.lastPos.z;
      const targetChanged = !cameraBindings
        || newTarget.x !== cameraBindings.lastTarget.x
        || newTarget.y !== cameraBindings.lastTarget.y
        || newTarget.z !== cameraBindings.lastTarget.z;
      const projChanged = !cameraBindings
        || newProj.type !== cameraBindings.lastProj.type
        || newProj.fov !== cameraBindings.lastProj.fov
        || newProj.size !== cameraBindings.lastProj.size
        || newProj.near !== cameraBindings.lastProj.near
        || newProj.far !== cameraBindings.lastProj.far;

      if (posChanged || targetChanged || projChanged) {
        const built = buildCameraMatrices(cameraData, aspect, newModel);
        projMat = built.projMat;
        viewMat = built.viewMat;
        cameraPos = built.cameraPos;
        if (cameraBindings) {
          cameraBindings.lastPos = newPos;
          cameraBindings.lastTarget = newTarget;
          cameraBindings.lastProj = newProj;
        }
        dirty = true;
      }
    }

    if (dirty) {
      pickDirty = hasPickables;  // mark pick buffer for re-render
      scheduleFrame();
    }
  };

  canvas.__glRender = () => renderScene(gl, programs, geoCache, texCache, fontCache, renderList, projMat, viewMat, lights, cameraPos);
  canvas.__glContext = gl;

  // --- Resize handling (HiDPI aware) ---
  function handleResize() {
    const dpr = window.devicePixelRatio || 1;
    const rect = canvas.getBoundingClientRect();
    const drawW = Math.round(rect.width * dpr);
    const drawH = Math.round(rect.height * dpr);

    // Skip if nothing changed
    if (canvas.width === drawW && canvas.height === drawH) return;

    canvas.width = drawW;
    canvas.height = drawH;

    // Update aspect ratio and rebuild projection
    aspect = drawW / drawH;
    const model = getModel ? getModel() : null;
    const built = buildCameraMatrices(cameraData, aspect, model);
    projMat = built.projMat;
    viewMat = built.viewMat;
    cameraPos = built.cameraPos;

    // Recreate pick framebuffer at new size
    if (hasPickables) {
      // Delete old resources
      if (pickFB) {
        gl.deleteTexture(pickFB.colorTex);
        gl.deleteRenderbuffer(pickFB.depthRb);
        gl.deleteFramebuffer(pickFB.fb);
      }
      pickFB = createPickFramebuffer(gl, drawW, drawH);
      pickDirty = true;
    }

    scheduleFrame();
  }

  new ResizeObserver(handleResize).observe(canvas);

  const bindingCount = glBindings.length;
  const pickCount = pickRegistry.map.size;
  const lightCount = lights.length;
  const animCount = animateNodes.length;
  console.log(`[reactive-gl] Initialized WebGL2 canvas (${canvas.width}x${canvas.height}), ${renderList.length} render entries, ${bindingCount} bindings, ${pickCount} pickable, ${lightCount} lights, ${animCount} animate`);
}

// ---------------------------------------------------------------------------
// Auto-initialization: observe DOM for canvases with __glScene
// ---------------------------------------------------------------------------

function initAllCanvases(root) {
  const canvases = root.querySelectorAll('canvas');
  for (const c of canvases) {
    if (c.__glScene && !c.__glContext) {
      initGLCanvas(c);
    }
  }
}

function startObserver() {
  initAllCanvases(document);

  const observer = new MutationObserver((mutations) => {
    for (const mut of mutations) {
      for (const node of mut.addedNodes) {
        if (node.nodeType !== Node.ELEMENT_NODE) continue;
        if (node.tagName === 'CANVAS' && node.__glScene) {
          initGLCanvas(node);
        }
        if (node.querySelectorAll) {
          initAllCanvases(node);
        }
      }
    }
  });

  observer.observe(document.body, { childList: true, subtree: true });
}

if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', startObserver);
} else {
  startObserver();
}

export { initGLCanvas };
