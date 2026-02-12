/**
 * Agdelte WebGL Runtime
 *
 * Interprets Scott-encoded Scene values from Agdelte.WebGL.Types
 * and renders them using WebGL2. Supports:
 */

// ---------------------------------------------------------------------------
// Configuration constants (centralized for maintainability)
// ---------------------------------------------------------------------------

const CONFIG = {
  MAX_LIGHTS: 8,               // Maximum lights per scene (matches shader arrays)
  MAX_LIST_ITEMS: 10000,       // Maximum items in Scott-encoded lists
  MAX_NAT_VALUE: 100000,       // Maximum for Scott-encoded natural numbers
  SPHERE_SLICES: 24,           // Sphere geometry horizontal segments
  SPHERE_STACKS: 16,           // Sphere geometry vertical segments
  CYLINDER_SEGMENTS: 24,       // Cylinder geometry segments
  FONT_ATLAS_SIZE: 1024,       // Font atlas texture size
  FONT_RENDER_SIZE: 48,        // Font rendering size for atlas
  PICK_HOVER_THROTTLE: 16,     // Hover event throttle (ms) ~60fps
  DRAG_THRESHOLD: 3,           // Pixels before drag starts
};

/**
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
    bindChildren: (extract, transform) => ({
      type: 'bindChildren',
      extract,           // Model → List (SceneNode Model Msg)
      transform: interpretTransform(transform)
    }),
    animate: (timeFn, child) => ({
      type: 'animate',
      timeFn,            // Float → Transform (Scott-encoded)
      child: interpretSceneNode(child)
    }),
    // Interactive group: all children share the same pick ID
    interactiveGroup: (attrs, transform, children) => ({
      type: 'interactiveGroup',
      attrs: listToArray(attrs).map(interpretSceneAttr),
      transform: interpretTransform(transform),
      children: listToArray(children).map(interpretSceneNode)
    }),
    // Named part: assigns a name for sub-ID picking within groups
    named: (name, child) => ({
      type: 'named',
      name,
      child: interpretSceneNode(child)
    }),
    // Instanced rendering: many copies with different transforms
    instanced: (geometry, material, transforms, handler) => ({
      type: 'instanced',
      geometry: interpretGeometry(geometry),
      material: interpretMaterial(material),
      transforms: listToArray(transforms).map(interpretTransform),
      handler  // ℕ → Msg (receives instance index on click)
    }),
    // Reactive instanced: transforms from model
    bindInstanced: (geometry, material, extract, handler) => ({
      type: 'bindInstanced',
      geometry: interpretGeometry(geometry),
      material: interpretMaterial(material),
      extract,  // Model → List Transform
      handler   // ℕ → Msg
    }),
    // Batched group: children merged into single draw call
    batched: (material, children, transform) => ({
      type: 'batched',
      material: interpretMaterial(material),
      children: listToArray(children).map(interpretSceneNode),
      transform: interpretTransform(transform)
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
    onMiddleDrag: (handler) => ({ type: 'onMiddleDrag', handler }),
    onScreenDrag: (handler) => ({ type: 'onScreenDrag', handler }),
    focusable: () => ({ type: 'focusable' }),
    onKeyDown: (handler) => ({ type: 'onKeyDown', handler }),
    onInput: (handler) => ({ type: 'onInput', handler }),
    transition: (duration, easing) => ({
      type: 'transition',
      durationMs: interpretDuration(duration),
      easing: interpretEasing(easing)
    }),
    animateOnHover: () => ({ type: 'animateOnHover' })
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
  for (let i = 0; i < CONFIG.MAX_NAT_VALUE; i++) {
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
  // Handle plain JS objects (from Geometry.Primitives like roundedBox)
  if (typeof geom === 'object' && geom !== null && geom.type) {
    return geom;
  }
  // Handle Scott-encoded geometry
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
  for (let i = 0; i < CONFIG.MAX_LIST_ITEMS; i++) {
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

// Shared GLSL snippets (DRY principle)
const GLSL_LIGHT_UNIFORMS = `
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
`;

// Attenuation calculation helper
const GLSL_ATTENUATION = `
float calcAttenuation(int lightIdx, vec3 worldPos) {
  if (u_lightType[lightIdx] == 0 || u_lightType[lightIdx] == 1) return 1.0;
  vec3 toLight = u_lightPos[lightIdx] - worldPos;
  float dist = length(toLight);
  float atten = clamp(1.0 - dist / max(u_lightRange[lightIdx], 0.001), 0.0, 1.0);
  atten *= atten;  // quadratic falloff
  if (u_lightType[lightIdx] == 3) {
    // Spot light cone
    vec3 L = toLight / max(dist, 0.001);
    vec3 spotDir = normalize(u_lightDir[lightIdx]);
    float cosAngle = dot(-L, spotDir);
    float cosOuter = cos(u_lightAngle[lightIdx]);
    float cosInner = cos(u_lightAngle[lightIdx] * (1.0 - u_lightFalloff[lightIdx]));
    atten *= clamp((cosAngle - cosOuter) / max(cosInner - cosOuter, 0.001), 0.0, 1.0);
  }
  return atten;
}

vec3 getLightDir(int lightIdx, vec3 worldPos) {
  if (u_lightType[lightIdx] == 1) return normalize(-u_lightDir[lightIdx]);
  return normalize(u_lightPos[lightIdx] - worldPos);
}
`;

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
    } else if (u_lightType[i] == 1) {
      // Directional (Blinn-Phong)
      vec3 L = normalize(-u_lightDir[i]);
      float diff = max(dot(N, L), 0.0);
      if (u_flatMode == 1) {
        // Flat material: diffuse only, no specular
        result += u_color.rgb * lc * diff;
      } else {
        vec3 H = normalize(L + V);
        float spec = pow(max(dot(N, H), 0.0), u_shininess);
        result += u_color.rgb * lc * diff + lc * spec;
      }
    } else if (u_lightType[i] == 2) {
      // Point light
      vec3 toLight = u_lightPos[i] - v_worldPos;
      float dist = length(toLight);
      vec3 L = toLight / max(dist, 0.001);
      float atten = clamp(1.0 - dist / max(u_lightRange[i], 0.001), 0.0, 1.0);
      atten *= atten;  // quadratic falloff
      float diff = max(dot(N, L), 0.0);
      if (u_flatMode == 1) {
        result += u_color.rgb * lc * diff * atten;
      } else {
        vec3 H = normalize(L + V);
        float spec = pow(max(dot(N, H), 0.0), u_shininess);
        result += (u_color.rgb * lc * diff + lc * spec) * atten;
      }
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
      if (u_flatMode == 1) {
        result += u_color.rgb * lc * diff * atten;
      } else {
        vec3 H = normalize(L + V);
        float spec = pow(max(dot(N, H), 0.0), u_shininess);
        result += (u_color.rgb * lc * diff + lc * spec) * atten;
      }
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

// Instanced rendering vertex shader — per-instance transforms via attributes
const INSTANCED_VERT_SRC = `#version 300 es
precision highp float;

layout(location = 0) in vec3 a_position;
layout(location = 1) in vec3 a_normal;
// Per-instance attributes (using mat4 as 4 vec4s for transform matrix)
layout(location = 2) in mat4 a_instanceMatrix;

uniform mat4 u_view;
uniform mat4 u_proj;

out vec3 v_normal;
out vec3 v_worldPos;
flat out int v_instanceId;

void main() {
  vec4 worldPos = a_instanceMatrix * vec4(a_position, 1.0);
  gl_Position = u_proj * u_view * worldPos;
  v_worldPos = worldPos.xyz;
  // Transform normal by inverse-transpose of instance matrix (approximation: just the rotation part)
  mat3 normalMat = mat3(a_instanceMatrix);
  v_normal = normalize(normalMat * a_normal);
  v_instanceId = gl_InstanceID;
}
`;

// Instanced pick shader — encodes pickId + instanceIndex in color
const INSTANCED_PICK_VERT_SRC = `#version 300 es
precision highp float;

layout(location = 0) in vec3 a_position;
layout(location = 2) in mat4 a_instanceMatrix;

uniform mat4 u_view;
uniform mat4 u_proj;

flat out int v_instanceId;

void main() {
  gl_Position = u_proj * u_view * a_instanceMatrix * vec4(a_position, 1.0);
  v_instanceId = gl_InstanceID;
}
`;

const INSTANCED_PICK_FRAG_SRC = `#version 300 es
precision highp float;

uniform int u_basePickId;

flat in int v_instanceId;

out vec4 fragColor;

void main() {
  int pickId = u_basePickId + v_instanceId;
  float r = float((pickId >>  0) & 0xFF) / 255.0;
  float g = float((pickId >>  8) & 0xFF) / 255.0;
  float b = float((pickId >> 16) & 0xFF) / 255.0;
  fragColor = vec4(r, g, b, 1.0);
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

// Textured shader — Phong-lit texture sampling (texture * tint as base color)
const TEX_VERT_SRC = `#version 300 es
precision highp float;

layout(location = 0) in vec3 a_position;
layout(location = 1) in vec3 a_normal;
layout(location = 2) in vec2 a_uv;

uniform mat4 u_model;
uniform mat4 u_view;
uniform mat4 u_proj;

out vec2 v_uv;
out vec3 v_normal;
out vec3 v_worldPos;

void main() {
  vec4 worldPos = u_model * vec4(a_position, 1.0);
  v_worldPos = worldPos.xyz;
  v_normal = normalize(mat3(u_model) * a_normal);
  v_uv = a_uv;
  gl_Position = u_proj * u_view * worldPos;
}
`;

const TEX_FRAG_SRC = `#version 300 es
precision highp float;

uniform sampler2D u_texture;
uniform vec4 u_color;  // tint
uniform float u_shininess;
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

in vec2 v_uv;
in vec3 v_normal;
in vec3 v_worldPos;

out vec4 fragColor;

void main() {
  vec4 texColor = texture(u_texture, v_uv);
  vec3 baseColor = texColor.rgb * u_color.rgb;

  vec3 N = normalize(v_normal);
  vec3 V = normalize(u_cameraPos - v_worldPos);
  vec3 result = vec3(0.0);

  for (int i = 0; i < 8; i++) {
    if (i >= u_numLights) break;
    vec3 lc = u_lightColor[i] * u_lightIntensity[i];

    if (u_lightType[i] == 0) {
      result += baseColor * lc;
    } else if (u_lightType[i] == 1) {
      vec3 L = normalize(-u_lightDir[i]);
      float diff = max(dot(N, L), 0.0);
      vec3 H = normalize(L + V);
      float spec = pow(max(dot(N, H), 0.0), u_shininess);
      result += baseColor * lc * diff + lc * spec;
    } else if (u_lightType[i] == 2) {
      vec3 toLight = u_lightPos[i] - v_worldPos;
      float dist = length(toLight);
      vec3 L = toLight / max(dist, 0.001);
      float atten = clamp(1.0 - dist / max(u_lightRange[i], 0.001), 0.0, 1.0);
      atten *= atten;
      float diff = max(dot(N, L), 0.0);
      vec3 H = normalize(L + V);
      float spec = pow(max(dot(N, H), 0.0), u_shininess);
      result += (baseColor * lc * diff + lc * spec) * atten;
    } else if (u_lightType[i] == 3) {
      vec3 toLight = u_lightPos[i] - v_worldPos;
      float dist = length(toLight);
      vec3 L = toLight / max(dist, 0.001);
      float atten = clamp(1.0 - dist / max(u_lightRange[i], 0.001), 0.0, 1.0);
      atten *= atten;
      vec3 spotDir = normalize(u_lightDir[i]);
      float cosAngle = dot(-L, spotDir);
      float cosOuter = cos(u_lightAngle[i]);
      float cosInner = cos(u_lightAngle[i] * (1.0 - u_lightFalloff[i]));
      float spotAtten = clamp((cosAngle - cosOuter) / max(cosInner - cosOuter, 0.001), 0.0, 1.0);
      atten *= spotAtten;
      float diff = max(dot(N, L), 0.0);
      vec3 H = normalize(L + V);
      float spec = pow(max(dot(N, H), 0.0), u_shininess);
      result += (baseColor * lc * diff + lc * spec) * atten;
    }
  }

  fragColor = vec4(result, texColor.a * u_color.a);
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
        localT = raySphere(localRay, { x: 0, y: 0, z: 0 }, geo.radius);
        break;
      }
      case 'box': {
        // Box geometry dims are full width; half-extents = dims/2
        const bd = geo.dims;
        localT = rayAABB(localRay, bd.x * 0.5, bd.y * 0.5, bd.z * 0.5);
        break;
      }
      case 'cylinder': {
        // Approximate cylinder as a box (height along Y)
        localT = rayAABB(localRay, geo.radius, geo.height * 0.5, geo.radius);
        break;
      }
      case 'plane': {
        localT = rayPlane(localRay);
        // Check bounds: plane extends to ±(size/2) in X and Z
        if (localT !== null) {
          const lp = rayAt(localRay, localT);
          const hw = geo.size.x * 0.5, hh = geo.size.y * 0.5;
          if (Math.abs(lp.x) > hw || Math.abs(lp.z) > hh) localT = null;
        }
        break;
      }
      case 'quad': {
        localT = rayPlane(localRay);
        if (localT !== null) {
          const lp = rayAt(localRay, localT);
          const qw = geo.size.x * 0.5, qh = geo.size.y * 0.5;
          if (Math.abs(lp.x) > qw || Math.abs(lp.z) > qh) localT = null;
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

/**
 * Find ray hit point for a specific pickId (handles groups with parent transforms).
 */
function rayPickForId(ray, renderList, targetPickId) {
  for (const entry of renderList) {
    if (entry.type === 'mesh' && entry.pickId === targetPickId) {
      const hit = rayIntersectEntry(ray, entry, null);
      if (hit) return hit.point;
    } else if (entry.type === 'group') {
      const result = rayPickGroupForId(ray, entry, null, targetPickId);
      if (result) return result;
    }
  }
  return null;
}

function rayPickGroupForId(ray, entry, parentMat, targetPickId) {
  if (entry.type === 'mesh') {
    if (entry.pickId === targetPickId) {
      const hit = rayIntersectEntry(ray, entry, parentMat);
      if (hit) return hit.point;
    }
  } else if (entry.type === 'group') {
    const tfm = entry.transform;
    const groupMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);
    for (const child of entry.children) {
      const result = rayPickGroupForId(ray, child, groupMat, targetPickId);
      if (result) return result;
    }
  }
  return null;
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
  // Each face: bottom-left, bottom-right, top-right, top-left
  const uvs = new Float32Array([
    0,0, 1,0, 1,1, 0,1,  // front
    0,0, 1,0, 1,1, 0,1,  // back
    0,0, 1,0, 1,1, 0,1,  // top
    0,0, 1,0, 1,1, 0,1,  // bottom
    0,0, 1,0, 1,1, 0,1,  // right
    0,0, 1,0, 1,1, 0,1,  // left
  ]);
  const indices = new Uint16Array([
     0,  1,  2,   0,  2,  3,
     4,  5,  6,   4,  6,  7,
     8,  9, 10,   8, 10, 11,
    12, 13, 14,  12, 14, 15,
    16, 17, 18,  16, 18, 19,
    20, 21, 22,  20, 22, 23,
  ]);
  return uploadGeometry(gl, positions, normals, indices, uvs);
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
  // Tile UVs based on size (1 unit = 1 tile repeat)
  const uvs = new Float32Array([0, 0, size.x, 0, size.x, size.y, 0, size.y]);
  const indices = new Uint16Array([0, 1, 2, 0, 2, 3]);
  return uploadGeometry(gl, positions, normals, indices, uvs);
}

function createCylinderGeometry(gl, radius, height) {
  const segments = 24;
  const positions = [], normals = [], indices = [];
  const hh = height * 0.5;
  // Side wall
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
  // Top cap
  const topCenter = positions.length / 3;
  positions.push(0, hh, 0);
  normals.push(0, 1, 0);
  for (let i = 0; i < segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    positions.push(radius * Math.cos(theta), hh, radius * Math.sin(theta));
    normals.push(0, 1, 0);
  }
  for (let i = 0; i < segments; i++) {
    const next = (i + 1) % segments;
    indices.push(topCenter, topCenter + 1 + i, topCenter + 1 + next);
  }
  // Bottom cap
  const botCenter = positions.length / 3;
  positions.push(0, -hh, 0);
  normals.push(0, -1, 0);
  for (let i = 0; i < segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    positions.push(radius * Math.cos(theta), -hh, radius * Math.sin(theta));
    normals.push(0, -1, 0);
  }
  for (let i = 0; i < segments; i++) {
    const next = (i + 1) % segments;
    indices.push(botCenter, botCenter + 1 + next, botCenter + 1 + i);
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
// Extended Primitives (from Builder.Geometry.Primitives)
// ---------------------------------------------------------------------------

/**
 * Create a torus (donut shape).
 * majorRadius: distance from center to tube center
 * minorRadius: tube radius
 * majorSegments: segments around the ring
 * minorSegments: segments around the tube
 */
function createTorusGeometry(gl, majorRadius, minorRadius, majorSegments, minorSegments) {
  const positions = [], normals = [], indices = [];
  for (let i = 0; i <= majorSegments; i++) {
    const u = (i / majorSegments) * 2 * Math.PI;
    const cosU = Math.cos(u), sinU = Math.sin(u);
    for (let j = 0; j <= minorSegments; j++) {
      const v = (j / minorSegments) * 2 * Math.PI;
      const cosV = Math.cos(v), sinV = Math.sin(v);
      const x = (majorRadius + minorRadius * cosV) * cosU;
      const y = minorRadius * sinV;
      const z = (majorRadius + minorRadius * cosV) * sinU;
      positions.push(x, y, z);
      // Normal points from tube center to surface
      const nx = cosV * cosU, ny = sinV, nz = cosV * sinU;
      normals.push(nx, ny, nz);
    }
  }
  for (let i = 0; i < majorSegments; i++) {
    for (let j = 0; j < minorSegments; j++) {
      const a = i * (minorSegments + 1) + j;
      const b = a + minorSegments + 1;
      indices.push(a, b, a + 1, b, b + 1, a + 1);
    }
  }
  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create a capsule (cylinder with hemispherical caps).
 */
function createCapsuleGeometry(gl, radius, height, segments) {
  const positions = [], normals = [], indices = [];
  const halfHeight = height * 0.5 - radius; // Cylinder height excluding caps
  const stacks = Math.floor(segments / 2);

  // Top hemisphere
  for (let s = 0; s <= stacks; s++) {
    const phi = (s / stacks) * (Math.PI / 2);
    const sinP = Math.sin(phi), cosP = Math.cos(phi);
    for (let l = 0; l <= segments; l++) {
      const theta = (l / segments) * 2 * Math.PI;
      const cosT = Math.cos(theta), sinT = Math.sin(theta);
      const nx = cosT * sinP, ny = cosP, nz = sinT * sinP;
      positions.push(radius * nx, halfHeight + radius * ny, radius * nz);
      normals.push(nx, ny, nz);
    }
  }

  // Cylinder body (two rings)
  const cylBase = positions.length / 3;
  for (let ring = 0; ring <= 1; ring++) {
    const y = ring === 0 ? halfHeight : -halfHeight;
    for (let l = 0; l <= segments; l++) {
      const theta = (l / segments) * 2 * Math.PI;
      const cosT = Math.cos(theta), sinT = Math.sin(theta);
      positions.push(radius * cosT, y, radius * sinT);
      normals.push(cosT, 0, sinT);
    }
  }

  // Bottom hemisphere
  const botBase = positions.length / 3;
  for (let s = 0; s <= stacks; s++) {
    const phi = (Math.PI / 2) + (s / stacks) * (Math.PI / 2);
    const sinP = Math.sin(phi), cosP = Math.cos(phi);
    for (let l = 0; l <= segments; l++) {
      const theta = (l / segments) * 2 * Math.PI;
      const cosT = Math.cos(theta), sinT = Math.sin(theta);
      const nx = cosT * sinP, ny = cosP, nz = sinT * sinP;
      positions.push(radius * nx, -halfHeight + radius * ny, radius * nz);
      normals.push(nx, ny, nz);
    }
  }

  // Indices for top hemisphere
  for (let s = 0; s < stacks; s++) {
    for (let l = 0; l < segments; l++) {
      const a = s * (segments + 1) + l;
      const b = a + segments + 1;
      indices.push(a, b, a + 1, b, b + 1, a + 1);
    }
  }

  // Indices for cylinder body
  for (let l = 0; l < segments; l++) {
    const a = cylBase + l;
    const b = a + segments + 1;
    indices.push(a, b, a + 1, b, b + 1, a + 1);
  }

  // Indices for bottom hemisphere
  for (let s = 0; s < stacks; s++) {
    for (let l = 0; l < segments; l++) {
      const a = botBase + s * (segments + 1) + l;
      const b = a + segments + 1;
      indices.push(a, b, a + 1, b, b + 1, a + 1);
    }
  }

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create a cone (tapered cylinder).
 * bottomRadius: radius at base
 * topRadius: radius at top (0 for pointed)
 * height: height of cone
 */
function createConeGeometry(gl, bottomRadius, topRadius, height, segments) {
  const positions = [], normals = [], indices = [];
  const hh = height * 0.5;
  const slope = (bottomRadius - topRadius) / height;

  // Side wall
  for (let i = 0; i <= segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    const cosT = Math.cos(theta), sinT = Math.sin(theta);
    // Normal is perpendicular to sloped surface
    const len = Math.sqrt(1 + slope * slope);
    const nx = cosT / len, ny = slope / len, nz = sinT / len;
    positions.push(topRadius * cosT, hh, topRadius * sinT);
    normals.push(nx, ny, nz);
    positions.push(bottomRadius * cosT, -hh, bottomRadius * sinT);
    normals.push(nx, ny, nz);
  }
  for (let i = 0; i < segments; i++) {
    const a = i * 2, b = a + 1, c = a + 2, d = a + 3;
    indices.push(a, b, c, b, d, c);
  }

  // Top cap (if not pointed)
  if (topRadius > 0.001) {
    const topCenter = positions.length / 3;
    positions.push(0, hh, 0);
    normals.push(0, 1, 0);
    for (let i = 0; i < segments; i++) {
      const theta = (i / segments) * 2 * Math.PI;
      positions.push(topRadius * Math.cos(theta), hh, topRadius * Math.sin(theta));
      normals.push(0, 1, 0);
    }
    for (let i = 0; i < segments; i++) {
      const next = (i + 1) % segments;
      indices.push(topCenter, topCenter + 1 + i, topCenter + 1 + next);
    }
  }

  // Bottom cap
  const botCenter = positions.length / 3;
  positions.push(0, -hh, 0);
  normals.push(0, -1, 0);
  for (let i = 0; i < segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    positions.push(bottomRadius * Math.cos(theta), -hh, bottomRadius * Math.sin(theta));
    normals.push(0, -1, 0);
  }
  for (let i = 0; i < segments; i++) {
    const next = (i + 1) % segments;
    indices.push(botCenter, botCenter + 1 + next, botCenter + 1 + i);
  }

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create an n-sided pyramid.
 */
function createPyramidGeometry(gl, baseSize, height, sides) {
  const positions = [], normals = [], indices = [];
  const hb = baseSize * 0.5;

  // Generate base vertices
  const baseVerts = [];
  for (let i = 0; i < sides; i++) {
    const theta = (i / sides) * 2 * Math.PI;
    baseVerts.push({ x: hb * Math.cos(theta), z: hb * Math.sin(theta) });
  }

  // Side faces
  const apex = { x: 0, y: height, z: 0 };
  for (let i = 0; i < sides; i++) {
    const v0 = baseVerts[i];
    const v1 = baseVerts[(i + 1) % sides];
    // Calculate face normal
    const e1 = { x: v1.x - v0.x, y: 0, z: v1.z - v0.z };
    const e2 = { x: apex.x - v0.x, y: apex.y, z: apex.z - v0.z };
    const nx = e1.y * e2.z - e1.z * e2.y;
    const ny = e1.z * e2.x - e1.x * e2.z;
    const nz = e1.x * e2.y - e1.y * e2.x;
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz);
    const normal = { x: nx / len, y: ny / len, z: nz / len };

    const idx = positions.length / 3;
    positions.push(v0.x, 0, v0.z, v1.x, 0, v1.z, apex.x, apex.y, apex.z);
    normals.push(normal.x, normal.y, normal.z, normal.x, normal.y, normal.z, normal.x, normal.y, normal.z);
    indices.push(idx, idx + 1, idx + 2);
  }

  // Base face
  const baseCenter = positions.length / 3;
  positions.push(0, 0, 0);
  normals.push(0, -1, 0);
  for (let i = 0; i < sides; i++) {
    positions.push(baseVerts[i].x, 0, baseVerts[i].z);
    normals.push(0, -1, 0);
  }
  for (let i = 0; i < sides; i++) {
    const next = (i + 1) % sides;
    indices.push(baseCenter, baseCenter + 1 + next, baseCenter + 1 + i);
  }

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create a tube (hollow cylinder/pipe).
 */
function createTubeGeometry(gl, innerRadius, outerRadius, height, segments) {
  const positions = [], normals = [], indices = [];
  const hh = height * 0.5;

  // Outer wall
  for (let i = 0; i <= segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    const cosT = Math.cos(theta), sinT = Math.sin(theta);
    positions.push(outerRadius * cosT, hh, outerRadius * sinT);
    normals.push(cosT, 0, sinT);
    positions.push(outerRadius * cosT, -hh, outerRadius * sinT);
    normals.push(cosT, 0, sinT);
  }
  for (let i = 0; i < segments; i++) {
    const a = i * 2, b = a + 1, c = a + 2, d = a + 3;
    indices.push(a, b, c, b, d, c);
  }

  // Inner wall (normals point inward)
  const innerBase = positions.length / 3;
  for (let i = 0; i <= segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    const cosT = Math.cos(theta), sinT = Math.sin(theta);
    positions.push(innerRadius * cosT, hh, innerRadius * sinT);
    normals.push(-cosT, 0, -sinT);
    positions.push(innerRadius * cosT, -hh, innerRadius * sinT);
    normals.push(-cosT, 0, -sinT);
  }
  for (let i = 0; i < segments; i++) {
    const a = innerBase + i * 2, b = a + 1, c = a + 2, d = a + 3;
    indices.push(a, c, b, b, c, d);  // Reversed winding
  }

  // Top ring
  const topBase = positions.length / 3;
  for (let i = 0; i <= segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    const cosT = Math.cos(theta), sinT = Math.sin(theta);
    positions.push(outerRadius * cosT, hh, outerRadius * sinT);
    normals.push(0, 1, 0);
    positions.push(innerRadius * cosT, hh, innerRadius * sinT);
    normals.push(0, 1, 0);
  }
  for (let i = 0; i < segments; i++) {
    const a = topBase + i * 2, b = a + 1, c = a + 2, d = a + 3;
    indices.push(a, b, c, b, d, c);
  }

  // Bottom ring
  const botBase = positions.length / 3;
  for (let i = 0; i <= segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    const cosT = Math.cos(theta), sinT = Math.sin(theta);
    positions.push(outerRadius * cosT, -hh, outerRadius * sinT);
    normals.push(0, -1, 0);
    positions.push(innerRadius * cosT, -hh, innerRadius * sinT);
    normals.push(0, -1, 0);
  }
  for (let i = 0; i < segments; i++) {
    const a = botBase + i * 2, b = a + 1, c = a + 2, d = a + 3;
    indices.push(a, c, b, b, c, d);  // Reversed for bottom
  }

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create a flat ring (2D washer shape in XZ plane).
 */
function createRingGeometry(gl, innerRadius, outerRadius, segments) {
  const positions = [], normals = [], indices = [];

  for (let i = 0; i <= segments; i++) {
    const theta = (i / segments) * 2 * Math.PI;
    const cosT = Math.cos(theta), sinT = Math.sin(theta);
    positions.push(outerRadius * cosT, 0, outerRadius * sinT);
    normals.push(0, 1, 0);
    positions.push(innerRadius * cosT, 0, innerRadius * sinT);
    normals.push(0, 1, 0);
  }
  for (let i = 0; i < segments; i++) {
    const a = i * 2, b = a + 1, c = a + 2, d = a + 3;
    indices.push(a, b, c, b, d, c);
  }

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create a tetrahedron (4 triangular faces).
 */
function createTetrahedronGeometry(gl, radius) {
  // Vertices of a regular tetrahedron
  const a = radius / Math.sqrt(3);
  const verts = [
    { x:  a,  y:  a,  z:  a },
    { x:  a,  y: -a,  z: -a },
    { x: -a,  y:  a,  z: -a },
    { x: -a,  y: -a,  z:  a },
  ];
  const faces = [[0, 1, 2], [0, 3, 1], [0, 2, 3], [1, 3, 2]];

  const positions = [], normals = [], indices = [];
  for (const [i0, i1, i2] of faces) {
    const v0 = verts[i0], v1 = verts[i1], v2 = verts[i2];
    // Compute face normal
    const e1 = { x: v1.x - v0.x, y: v1.y - v0.y, z: v1.z - v0.z };
    const e2 = { x: v2.x - v0.x, y: v2.y - v0.y, z: v2.z - v0.z };
    const nx = e1.y * e2.z - e1.z * e2.y;
    const ny = e1.z * e2.x - e1.x * e2.z;
    const nz = e1.x * e2.y - e1.y * e2.x;
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz);
    const n = { x: nx / len, y: ny / len, z: nz / len };

    const idx = positions.length / 3;
    positions.push(v0.x, v0.y, v0.z, v1.x, v1.y, v1.z, v2.x, v2.y, v2.z);
    normals.push(n.x, n.y, n.z, n.x, n.y, n.z, n.x, n.y, n.z);
    indices.push(idx, idx + 1, idx + 2);
  }

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create an octahedron (8 triangular faces).
 */
function createOctahedronGeometry(gl, radius) {
  const verts = [
    { x: radius, y: 0, z: 0 },
    { x: -radius, y: 0, z: 0 },
    { x: 0, y: radius, z: 0 },
    { x: 0, y: -radius, z: 0 },
    { x: 0, y: 0, z: radius },
    { x: 0, y: 0, z: -radius },
  ];
  const faces = [
    [0, 2, 4], [0, 4, 3], [0, 3, 5], [0, 5, 2],
    [1, 4, 2], [1, 3, 4], [1, 5, 3], [1, 2, 5],
  ];

  const positions = [], normals = [], indices = [];
  for (const [i0, i1, i2] of faces) {
    const v0 = verts[i0], v1 = verts[i1], v2 = verts[i2];
    const e1 = { x: v1.x - v0.x, y: v1.y - v0.y, z: v1.z - v0.z };
    const e2 = { x: v2.x - v0.x, y: v2.y - v0.y, z: v2.z - v0.z };
    const nx = e1.y * e2.z - e1.z * e2.y;
    const ny = e1.z * e2.x - e1.x * e2.z;
    const nz = e1.x * e2.y - e1.y * e2.x;
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz);
    const n = { x: nx / len, y: ny / len, z: nz / len };

    const idx = positions.length / 3;
    positions.push(v0.x, v0.y, v0.z, v1.x, v1.y, v1.z, v2.x, v2.y, v2.z);
    normals.push(n.x, n.y, n.z, n.x, n.y, n.z, n.x, n.y, n.z);
    indices.push(idx, idx + 1, idx + 2);
  }

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create an icosahedron (20 triangular faces).
 */
function createIcosahedronGeometry(gl, radius) {
  const t = (1 + Math.sqrt(5)) / 2;  // Golden ratio
  const s = radius / Math.sqrt(1 + t * t);
  const verts = [
    { x: -s, y:  t*s, z: 0 }, { x:  s, y:  t*s, z: 0 },
    { x: -s, y: -t*s, z: 0 }, { x:  s, y: -t*s, z: 0 },
    { x: 0, y: -s, z:  t*s }, { x: 0, y:  s, z:  t*s },
    { x: 0, y: -s, z: -t*s }, { x: 0, y:  s, z: -t*s },
    { x:  t*s, y: 0, z: -s }, { x:  t*s, y: 0, z:  s },
    { x: -t*s, y: 0, z: -s }, { x: -t*s, y: 0, z:  s },
  ];
  const faces = [
    [0, 11, 5], [0, 5, 1], [0, 1, 7], [0, 7, 10], [0, 10, 11],
    [1, 5, 9], [5, 11, 4], [11, 10, 2], [10, 7, 6], [7, 1, 8],
    [3, 9, 4], [3, 4, 2], [3, 2, 6], [3, 6, 8], [3, 8, 9],
    [4, 9, 5], [2, 4, 11], [6, 2, 10], [8, 6, 7], [9, 8, 1],
  ];

  const positions = [], normals = [], indices = [];
  for (const [i0, i1, i2] of faces) {
    const v0 = verts[i0], v1 = verts[i1], v2 = verts[i2];
    const e1 = { x: v1.x - v0.x, y: v1.y - v0.y, z: v1.z - v0.z };
    const e2 = { x: v2.x - v0.x, y: v2.y - v0.y, z: v2.z - v0.z };
    const nx = e1.y * e2.z - e1.z * e2.y;
    const ny = e1.z * e2.x - e1.x * e2.z;
    const nz = e1.x * e2.y - e1.y * e2.x;
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz);
    const n = { x: nx / len, y: ny / len, z: nz / len };

    const idx = positions.length / 3;
    positions.push(v0.x, v0.y, v0.z, v1.x, v1.y, v1.z, v2.x, v2.y, v2.z);
    normals.push(n.x, n.y, n.z, n.x, n.y, n.z, n.x, n.y, n.z);
    indices.push(idx, idx + 1, idx + 2);
  }

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create a dodecahedron (12 pentagonal faces, triangulated = 36 triangles).
 */
function createDodecahedronGeometry(gl, radius) {
  const t = (1 + Math.sqrt(5)) / 2;
  const s = radius / Math.sqrt(3);
  const a = s, b = s / t, c = s * t;

  const verts = [
    { x: a, y: a, z: a }, { x: a, y: a, z: -a }, { x: a, y: -a, z: a }, { x: a, y: -a, z: -a },
    { x: -a, y: a, z: a }, { x: -a, y: a, z: -a }, { x: -a, y: -a, z: a }, { x: -a, y: -a, z: -a },
    { x: 0, y: b, z: c }, { x: 0, y: b, z: -c }, { x: 0, y: -b, z: c }, { x: 0, y: -b, z: -c },
    { x: b, y: c, z: 0 }, { x: b, y: -c, z: 0 }, { x: -b, y: c, z: 0 }, { x: -b, y: -c, z: 0 },
    { x: c, y: 0, z: b }, { x: c, y: 0, z: -b }, { x: -c, y: 0, z: b }, { x: -c, y: 0, z: -b },
  ];

  // Pentagonal faces (vertex indices)
  const pentagons = [
    [0, 16, 2, 10, 8], [0, 8, 4, 14, 12], [16, 0, 12, 1, 17],
    [1, 12, 14, 5, 9], [2, 16, 17, 3, 13], [13, 3, 11, 7, 15],
    [3, 17, 1, 9, 11], [4, 8, 10, 6, 18], [14, 4, 18, 19, 5],
    [5, 19, 7, 11, 9], [6, 10, 2, 13, 15], [7, 19, 18, 6, 15],
  ];

  const positions = [], normals = [], indices = [];

  for (const pent of pentagons) {
    // Calculate center and normal
    let cx = 0, cy = 0, cz = 0;
    for (const i of pent) {
      cx += verts[i].x; cy += verts[i].y; cz += verts[i].z;
    }
    cx /= 5; cy /= 5; cz /= 5;

    const v0 = verts[pent[0]], v1 = verts[pent[1]], v2 = verts[pent[2]];
    const e1 = { x: v1.x - v0.x, y: v1.y - v0.y, z: v1.z - v0.z };
    const e2 = { x: v2.x - v0.x, y: v2.y - v0.y, z: v2.z - v0.z };
    let nx = e1.y * e2.z - e1.z * e2.y;
    let ny = e1.z * e2.x - e1.x * e2.z;
    let nz = e1.x * e2.y - e1.y * e2.x;
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz);
    nx /= len; ny /= len; nz /= len;

    // Fan triangulation from center
    const centerIdx = positions.length / 3;
    positions.push(cx, cy, cz);
    normals.push(nx, ny, nz);

    for (const i of pent) {
      positions.push(verts[i].x, verts[i].y, verts[i].z);
      normals.push(nx, ny, nz);
    }

    for (let i = 0; i < 5; i++) {
      const next = (i + 1) % 5;
      indices.push(centerIdx, centerIdx + 1 + i, centerIdx + 1 + next);
    }
  }

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
}

/**
 * Create a rounded box (box with beveled edges).
 * Simplified: uses bevel by offsetting corner vertices.
 */
function createRoundedBoxGeometry(gl, dims, radius, segments) {
  // Rounded box as a single continuous mesh using ray-SDF intersection.
  // Each face of a subdivided cube is projected onto the rounded box surface.
  const hw = Math.max(dims.x * 0.5 - radius, 0);
  const hh = Math.max(dims.y * 0.5 - radius, 0);
  const hd = Math.max(dims.z * 0.5 - radius, 0);
  const r = Math.max(radius, 0.001);
  const segs = Math.max(segments * 4, 12);

  const positions = [], normals = [], indices = [];

  // Find t>0 where ray t*d hits the rounded box surface: SDF(t*d) = 0
  // SDF(p) = length(max(|p| - half, 0)) - r
  function solveT(dx, dy, dz) {
    const ax = Math.abs(dx), ay = Math.abs(dy), az = Math.abs(dz);

    // Case 1: only one axis exceeds the box (flat face region)
    // Z dominant
    if (az > 0.0001) { const t = (hd + r) / az; if (t * ax <= hw + 1e-6 && t * ay <= hh + 1e-6) return t; }
    // Y dominant
    if (ay > 0.0001) { const t = (hh + r) / ay; if (t * ax <= hw + 1e-6 && t * az <= hd + 1e-6) return t; }
    // X dominant
    if (ax > 0.0001) { const t = (hw + r) / ax; if (t * ay <= hh + 1e-6 && t * az <= hd + 1e-6) return t; }

    // Case 2: two axes exceed (edge region) — solve quadratic
    function solveEdge(a1, h1, a2, h2, aOther, hOther) {
      const A = a1 * a1 + a2 * a2;
      if (A < 1e-12) return null;
      const B = -2 * (a1 * h1 + a2 * h2);
      const C = h1 * h1 + h2 * h2 - r * r;
      const disc = B * B - 4 * A * C;
      if (disc < 0) return null;
      const t = (-B + Math.sqrt(disc)) / (2 * A);
      if (t > 0 && t * aOther <= hOther + 1e-6) return t;
      return null;
    }
    let t;
    t = solveEdge(ax, hw, az, hd, ay, hh); if (t) return t;  // XZ edge
    t = solveEdge(ax, hw, ay, hh, az, hd); if (t) return t;  // XY edge
    t = solveEdge(ay, hh, az, hd, ax, hw); if (t) return t;  // YZ edge

    // Case 3: all three axes exceed (corner region) — solve quadratic
    const A3 = ax * ax + ay * ay + az * az; // = 1 for normalized d
    const B3 = -2 * (ax * hw + ay * hh + az * hd);
    const C3 = hw * hw + hh * hh + hd * hd - r * r;
    const disc3 = B3 * B3 - 4 * A3 * C3;
    if (disc3 >= 0) return (-B3 + Math.sqrt(disc3)) / (2 * A3);

    return 1; // fallback
  }

  // Generate one face of the subdivided cube, projected onto the rounded box
  function addFace(mapUV, flip) {
    const base = positions.length / 3;
    for (let i = 0; i <= segs; i++) {
      for (let j = 0; j <= segs; j++) {
        const u = (2 * i / segs) - 1, v = (2 * j / segs) - 1;
        const cp = mapUV(u, v);  // point on cube face
        const len = Math.sqrt(cp[0] * cp[0] + cp[1] * cp[1] + cp[2] * cp[2]);
        const dx = cp[0] / len, dy = cp[1] / len, dz = cp[2] / len;

        const t = solveT(dx, dy, dz);
        const px = dx * t, py = dy * t, pz = dz * t;

        // SDF gradient = outward normal
        const qx = Math.max(Math.abs(px) - hw, 0) * (px >= 0 ? 1 : -1);
        const qy = Math.max(Math.abs(py) - hh, 0) * (py >= 0 ? 1 : -1);
        const qz = Math.max(Math.abs(pz) - hd, 0) * (pz >= 0 ? 1 : -1);
        const qLen = Math.sqrt(qx * qx + qy * qy + qz * qz);
        const nx = qLen > 1e-6 ? qx / qLen : dx;
        const ny = qLen > 1e-6 ? qy / qLen : dy;
        const nz = qLen > 1e-6 ? qz / qLen : dz;

        positions.push(px, py, pz);
        normals.push(nx, ny, nz);
      }
    }
    for (let i = 0; i < segs; i++) {
      for (let j = 0; j < segs; j++) {
        const a = base + i * (segs + 1) + j;
        const b = a + segs + 1;
        if (!flip) {
          indices.push(a, b, a + 1, b, b + 1, a + 1);
        } else {
          indices.push(a, a + 1, b, b, a + 1, b + 1);
        }
      }
    }
  }

  const sx = hw + r, sy = hh + r, sz = hd + r;

  addFace((u, v) => [u * sx, v * sy,  sz], false);  // +Z front
  addFace((u, v) => [u * sx, v * sy, -sz], true);   // -Z back
  addFace((u, v) => [u * sx,  sy, v * sz], true);   // +Y top
  addFace((u, v) => [u * sx, -sy, v * sz], false);  // -Y bottom
  addFace((u, v) => [ sx, v * sy, u * sz], true);   // +X right
  addFace((u, v) => [-sx, v * sy, u * sz], false);  // -X left

  return uploadGeometry(gl, new Float32Array(positions), new Float32Array(normals), new Uint16Array(indices));
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
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.REPEAT);
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
  const atlasSize = 1024;
  const canvas2d = document.createElement('canvas');
  canvas2d.width = atlasSize;
  canvas2d.height = atlasSize;
  const ctx = canvas2d.getContext('2d');

  // Font setup — render at high resolution for quality
  const renderSize = Math.max(48, fontSize);
  ctx.font = `${renderSize}px ${fontFamily}`;
  ctx.textBaseline = 'alphabetic';
  ctx.fillStyle = 'white';

  // ASCII range 32-126 + some useful Unicode
  const chars = [];
  for (let i = 32; i <= 126; i++) chars.push(String.fromCharCode(i));
  // Add a few common Unicode chars
  for (const c of '…—–·×÷±≤≥≠∞°') chars.push(c);

  const padding = 4;
  let curX = padding, curY = padding;
  let rowHeight = 0;
  const glyphs = new Map();

  // Measure full line height including descenders using a string with ascenders+descenders
  const fullMetrics = ctx.measureText('Mgypq|');
  const ascent = fullMetrics.actualBoundingBoxAscent || renderSize * 0.8;
  const descent = fullMetrics.actualBoundingBoxDescent || renderSize * 0.2;
  const lineHeight = ascent + descent;

  for (const ch of chars) {
    const m = ctx.measureText(ch);
    // Use actual bounding box width for proper glyph cell sizing
    const bbLeft = m.actualBoundingBoxLeft || 0;
    const bbRight = m.actualBoundingBoxRight || m.width;
    const glyphW = Math.ceil(bbLeft + bbRight);
    const w = glyphW + padding * 2;
    const h = Math.ceil(lineHeight) + padding * 2;

    if (curX + w > atlasSize) {
      curX = padding;
      curY += rowHeight + padding;
      rowHeight = 0;
    }
    if (curY + h > atlasSize) break; // atlas full

    // Draw glyph with alphabetic baseline positioned so full ascent+descent fits
    const drawX = curX + padding + bbLeft;
    const drawY = curY + padding + Math.ceil(ascent);
    ctx.fillText(ch, drawX, drawY);
    glyphs.set(ch, {
      x: curX, y: curY,
      w, h,
      advance: m.width / renderSize, // normalized to unit size
      xOff: -bbLeft / renderSize,
      yOff: 0,
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
  const uniforms = {
    model:     gl.getUniformLocation(prog, 'u_model'),
    view:      gl.getUniformLocation(prog, 'u_view'),
    proj:      gl.getUniformLocation(prog, 'u_proj'),
    color:     gl.getUniformLocation(prog, 'u_color'),
    texture:   gl.getUniformLocation(prog, 'u_texture'),
    shininess: gl.getUniformLocation(prog, 'u_shininess'),
    cameraPos: gl.getUniformLocation(prog, 'u_cameraPos'),
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
 * Create instanced phong shader program.
 * Uses per-instance matrix attributes instead of model uniform.
 */
function createInstancedPhongProgram(gl) {
  const vert = compileShader(gl, gl.VERTEX_SHADER, INSTANCED_VERT_SRC);
  const frag = compileShader(gl, gl.FRAGMENT_SHADER, PHONG_FRAG_SRC);
  const prog = gl.createProgram();
  gl.attachShader(prog, vert);
  gl.attachShader(prog, frag);
  gl.linkProgram(prog);
  if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
    const log = gl.getProgramInfoLog(prog);
    gl.deleteProgram(prog);
    throw new Error('Instanced phong program link error: ' + log);
  }
  const uniforms = {
    view:      gl.getUniformLocation(prog, 'u_view'),
    proj:      gl.getUniformLocation(prog, 'u_proj'),
    color:     gl.getUniformLocation(prog, 'u_color'),
    shininess: gl.getUniformLocation(prog, 'u_shininess'),
    cameraPos: gl.getUniformLocation(prog, 'u_cameraPos'),
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

/**
 * Create instanced pick shader program.
 * Renders each instance with pickId = basePickId + instanceIndex.
 */
function createInstancedPickProgram(gl) {
  const vert = compileShader(gl, gl.VERTEX_SHADER, INSTANCED_PICK_VERT_SRC);
  const frag = compileShader(gl, gl.FRAGMENT_SHADER, INSTANCED_PICK_FRAG_SRC);
  const prog = gl.createProgram();
  gl.attachShader(prog, vert);
  gl.attachShader(prog, frag);
  gl.linkProgram(prog);
  if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
    const log = gl.getProgramInfoLog(prog);
    gl.deleteProgram(prog);
    throw new Error('Instanced pick program link error: ' + log);
  }
  return {
    program: prog,
    uniforms: {
      view:       gl.getUniformLocation(prog, 'u_view'),
      proj:       gl.getUniformLocation(prog, 'u_proj'),
      basePickId: gl.getUniformLocation(prog, 'u_basePickId'),
    }
  };
}

/**
 * Create offscreen framebuffer for color picking.
 * Renders at full canvas resolution with RGBA8 color + depth.
 */
function createPickFramebuffer(gl, width, height) {
  if (width <= 0 || height <= 0) return null;
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
    // Extended primitives
    case 'roundedBox': return `roundedBox:${geom.dims.x},${geom.dims.y},${geom.dims.z},${geom.radius},${geom.segments}`;
    case 'capsule':    return `capsule:${geom.radius},${geom.height},${geom.segments}`;
    case 'torus':      return `torus:${geom.majorRadius},${geom.minorRadius},${geom.majorSegments},${geom.minorSegments}`;
    case 'cone':       return `cone:${geom.bottomRadius},${geom.topRadius},${geom.height},${geom.segments}`;
    case 'pyramid':    return `pyramid:${geom.baseSize},${geom.height},${geom.sides}`;
    case 'tube':       return `tube:${geom.innerRadius},${geom.outerRadius},${geom.height},${geom.segments}`;
    case 'ring':       return `ring:${geom.innerRadius},${geom.outerRadius},${geom.segments}`;
    case 'icosahedron':  return `icosahedron:${geom.radius}`;
    case 'dodecahedron': return `dodecahedron:${geom.radius}`;
    case 'octahedron':   return `octahedron:${geom.radius}`;
    case 'tetrahedron':  return `tetrahedron:${geom.radius}`;
    default:         return null;
  }
}

function getOrCreateGeometry(gl, cache, geom) {
  const key = geometryKey(geom);
  if (key && cache.has(key)) return cache.get(key);
  let result;
  switch (geom.type) {
    case 'box':         result = createBoxGeometry(gl, geom.dims); break;
    case 'sphere':      result = createSphereGeometry(gl, geom.radius); break;
    case 'plane':       result = createPlaneGeometry(gl, geom.size); break;
    case 'cylinder':    result = createCylinderGeometry(gl, geom.radius, geom.height); break;
    case 'quad':        result = createQuadGeometry(gl, geom.size); break;
    case 'custom':      result = geom.handle; break;  // handle IS the {vao, count} object
    // Extended primitives from Builder.Geometry.Primitives
    case 'torus':       result = createTorusGeometry(gl, geom.majorRadius, geom.minorRadius, geom.majorSegments, geom.minorSegments); break;
    case 'capsule':     result = createCapsuleGeometry(gl, geom.radius, geom.height, geom.segments); break;
    case 'cone':        result = createConeGeometry(gl, geom.bottomRadius, geom.topRadius, geom.height, geom.segments); break;
    case 'pyramid':     result = createPyramidGeometry(gl, geom.baseSize, geom.height, geom.sides); break;
    case 'tube':        result = createTubeGeometry(gl, geom.innerRadius, geom.outerRadius, geom.height, geom.segments); break;
    case 'ring':        result = createRingGeometry(gl, geom.innerRadius, geom.outerRadius, geom.segments); break;
    case 'roundedBox':  result = createRoundedBoxGeometry(gl, geom.dims, geom.radius, geom.segments); break;
    case 'tetrahedron': result = createTetrahedronGeometry(gl, geom.radius); break;
    case 'octahedron':  result = createOctahedronGeometry(gl, geom.radius); break;
    case 'icosahedron': result = createIcosahedronGeometry(gl, geom.radius); break;
    case 'dodecahedron': result = createDodecahedronGeometry(gl, geom.radius); break;
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

/**
 * Search for a transition attr in a scene node subtree.
 * If the node has attrs, check them directly.
 * If the node is a group/animate (no attrs), search its children/child.
 */
function findTransitionInSubtree(node) {
  if (!node) return null;
  // Stop at bindTransform boundaries — each bindTransform finds its own transition
  if (node.type === 'bindTransform') return null;
  if (node.attrs) return findTransition(node.attrs);
  // group: check children
  if (node.type === 'group' && node.children) {
    for (const child of node.children) {
      const t = findTransitionInSubtree(child);
      if (t) return t;
    }
  }
  // animate: check single child
  if (node.child) return findTransitionInSubtree(node.child);
  return null;
}

// ---------------------------------------------------------------------------
// Instanced Rendering — per-instance transform matrices
// ---------------------------------------------------------------------------

/**
 * Build a Float32Array containing 4x4 transform matrices for each instance.
 * Each transform = { pos, rot, scale } is converted to a mat4.
 */
function buildInstanceMatrices(transforms) {
  const count = transforms.length;
  const data = new Float32Array(count * 16);
  for (let i = 0; i < count; i++) {
    const t = transforms[i];
    // Build mat4 from transform (position, rotation quat, scale)
    const mat = transformToMat4(t);
    data.set(mat, i * 16);
  }
  return data;
}

/**
 * Convert an interpreted transform to a Float32Array mat4.
 */
function transformToMat4(t) {
  const { pos, rot, scale } = t;
  // Build rotation matrix from quaternion
  const { x: qx, y: qy, z: qz, w: qw } = rot;
  const xx = qx * qx, yy = qy * qy, zz = qz * qz;
  const xy = qx * qy, xz = qx * qz, yz = qy * qz;
  const wx = qw * qx, wy = qw * qy, wz = qw * qz;

  // Column-major mat4 = scale * rot * translate
  // For WebGL, column-major order
  return new Float32Array([
    (1 - 2 * (yy + zz)) * scale.x,
    2 * (xy + wz) * scale.x,
    2 * (xz - wy) * scale.x,
    0,

    2 * (xy - wz) * scale.y,
    (1 - 2 * (xx + zz)) * scale.y,
    2 * (yz + wx) * scale.y,
    0,

    2 * (xz + wy) * scale.z,
    2 * (yz - wx) * scale.z,
    (1 - 2 * (xx + yy)) * scale.z,
    0,

    pos.x,
    pos.y,
    pos.z,
    1
  ]);
}

/**
 * Create or update an instance buffer for instanced rendering.
 * Returns { buffer, count }.
 */
function createInstanceBuffer(gl, transforms) {
  const data = buildInstanceMatrices(transforms);
  const buffer = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
  gl.bufferData(gl.ARRAY_BUFFER, data, gl.DYNAMIC_DRAW);
  return { buffer, count: transforms.length };
}

/**
 * Update an existing instance buffer with new transforms.
 */
function updateInstanceBuffer(gl, buffer, transforms) {
  const data = buildInstanceMatrices(transforms);
  gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
  gl.bufferData(gl.ARRAY_BUFFER, data, gl.DYNAMIC_DRAW);
}

/**
 * Set up instance matrix attributes for instanced rendering.
 * Instance matrix uses attribute locations 2-5 (mat4 = 4 vec4s).
 */
function setupInstanceAttributes(gl, instanceBuffer) {
  gl.bindBuffer(gl.ARRAY_BUFFER, instanceBuffer);
  const bytesPerMatrix = 4 * 16; // 16 floats * 4 bytes per float
  for (let i = 0; i < 4; i++) {
    const loc = 2 + i;
    gl.enableVertexAttribArray(loc);
    gl.vertexAttribPointer(loc, 4, gl.FLOAT, false, bytesPerMatrix, i * 16);
    gl.vertexAttribDivisor(loc, 1); // Advance once per instance
  }
}

/**
 * Disable instance matrix attributes.
 */
function disableInstanceAttributes(gl) {
  for (let i = 0; i < 4; i++) {
    gl.disableVertexAttribArray(2 + i);
    gl.vertexAttribDivisor(2 + i, 0);
  }
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

    case 'bindChildren': {
      // Extract children list from model and interpret each child
      const scottChildren = node.extract(model);
      const childrenArray = listToArray(scottChildren);

      // Track starting positions so we can replace children on update
      const renderStartIdx = renderList.length;
      const pickStartSize = pickRegistry.map.size;
      const lightsStartIdx = lights.length;

      // Interpret and collect each child - pass null to let each child use its own transform
      for (const scottChild of childrenArray) {
        const interpretedChild = interpretSceneNode(scottChild);
        collectNode(interpretedChild, null, renderList, bindings, model, pickRegistry, lights, animateNodes);
      }

      // Register binding for dynamic updates
      bindings.push({
        type: 'children',
        extract: node.extract,
        transform: node.transform,
        renderListRef: renderList,
        pickRegistryRef: pickRegistry,
        lightsRef: lights,
        animateNodesRef: animateNodes,
        bindings: bindings,
        // Track what we added
        renderStartIdx: renderStartIdx,
        renderCount: renderList.length - renderStartIdx,
        lightsStartIdx: lightsStartIdx,
        lightsCount: lights.length - lightsStartIdx,
        pickStartSize: pickStartSize,
      });
      break;
    }

    case 'animate': {
      // Evaluate the time function at t=0 for initial transform
      const scottTransform = node.timeFn(0.0);
      const initialTransform = interpretTransform(scottTransform);

      // If a parent bindTransform provides an override, compose it with the
      // animated transform by adding positions together. Store the override
      // so tickAnimateNodes can compose each frame.
      const baseOffset = overrideTransform || null;
      const composedInitial = baseOffset
        ? { pos: { x: initialTransform.pos.x + baseOffset.pos.x,
                    y: initialTransform.pos.y + baseOffset.pos.y,
                    z: initialTransform.pos.z + baseOffset.pos.z },
            rot: initialTransform.rot, scale: initialTransform.scale }
        : initialTransform;

      // Process child with composed transform
      const childEntries = [];
      const lightsBefore = lights.length;
      collectNode(node.child, composedInitial, childEntries, bindings, model, pickRegistry, lights, animateNodes);
      const lightsAfter = lights.length;

      // Register animate node: each frame, call timeFn(t) and update child entries
      const animEntry = {
        timeFn: node.timeFn,
        targets: childEntries,
        baseOffset,   // stored for composing in tickAnimateNodes
      };

      // If the child added lights, track their indices so we can update
      // their positions each frame from the animated transform
      if (lightsAfter > lightsBefore) {
        animEntry.lightIndices = [];
        animEntry.lightsRef = lights;
        for (let i = lightsBefore; i < lightsAfter; i++) {
          animEntry.lightIndices.push(i);
        }
      }

      // Check if any child entry has animateOnHover attr — if so, this
      // animate node only ticks while its children are hovered.
      let isHoverOnly = false;
      const hoverPickIds = new Set();
      for (const ce of childEntries) {
        if (ce.pickId != null) {
          const reg = pickRegistry.map.get(ce.pickId);
          if (reg && reg.attrs) {
            for (const a of reg.attrs) {
              if (a.type === 'animateOnHover') {
                isHoverOnly = true;
              }
            }
          }
          if (isHoverOnly) hoverPickIds.add(ce.pickId);
        }
      }
      if (isHoverOnly) {
        animEntry.hoverOnly = true;
        animEntry.hoverPickIds = hoverPickIds;
        animEntry.accumTime = 0;      // accumulated hover time in seconds
        animEntry.lastTimestamp = null; // last frame timestamp when hovered
      }

      animateNodes.push(animEntry);

      renderList.push(...childEntries);
      break;
    }

    case 'bindTransform': {
      // Extract initial transform from model
      const scottTransform = node.extract(model);
      const initialTransform = interpretTransform(scottTransform);

      // Create a mutable render entry from the child
      // The child could be a mesh, bindMaterial, group, animate, etc.
      const childEntries = [];
      const animBefore = animateNodes.length;
      collectNode(node.child, initialTransform, childEntries, bindings, model, pickRegistry, lights, animateNodes);
      const animAfter = animateNodes.length;

      // If the child added animate entries, collect them so we can update their
      // baseOffset when the model changes (compose bindTransform + animate).
      const childAnimEntries = [];
      for (let i = animBefore; i < animAfter; i++) {
        childAnimEntries.push(animateNodes[i]);
      }

      // Look for transition spec in child's attrs (search into groups/animate)
      const trans = findTransitionInSubtree(node.child);

      // Register binding: on model change, re-extract and update all child entries
      bindings.push({
        type: 'transform',
        extract: node.extract,
        lastValue: initialTransform,
        targets: childEntries,  // entries whose transform we update
        childAnimEntries,       // animate entries to update baseOffset on
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

    case 'interactiveGroup': {
      // All children share the same pick ID (group-level interaction)
      const groupTransform = overrideTransform || node.transform;
      const children = [];
      // Temporarily disable pick registration for children
      const tempRegistry = { nextId: pickRegistry.nextId, map: new Map() };
      for (const child of node.children) {
        collectNode(child, null, children, bindings, model, tempRegistry, lights, animateNodes);
      }
      // Children get collected but don't have their own pickIds
      const entry = {
        type: 'group',
        transform: groupTransform,
        children,
        isInteractive: true,
      };
      // Register the group itself with the attrs
      registerPickable(entry, node.attrs, pickRegistry);
      renderList.push(entry);
      break;
    }

    case 'named': {
      // Named part for sub-ID picking within groups
      // For now, just pass through to child (sub-ID picking is future enhancement)
      collectNode(node.child, overrideTransform, renderList, bindings, model, pickRegistry, lights, animateNodes);
      break;
    }

    case 'instanced': {
      // WebGL2 instanced rendering: single draw call for many instances
      const entry = {
        type: 'instanced',
        geometry: node.geometry,
        material: node.material,
        transforms: node.transforms,
        handler: node.handler,
        // Each instance gets a unique pick ID range for clicking
        basePickId: pickRegistry.nextId,
      };
      // Register each instance for picking
      for (let i = 0; i < node.transforms.length; i++) {
        const instancePickId = pickRegistry.nextId++;
        pickRegistry.map.set(instancePickId, {
          entry,
          instanceIndex: i,
          attrs: [{ type: 'onClick', handler: () => node.handler(BigInt(i)) }]
        });
      }
      renderList.push(entry);
      break;
    }

    case 'bindInstanced': {
      // Extract initial transforms from model
      const scottTransforms = node.extract(model);
      const initialTransforms = listToArray(scottTransforms).map(interpretTransform);

      const entry = {
        type: 'instanced',
        geometry: node.geometry,
        material: node.material,
        transforms: initialTransforms,
        handler: node.handler,
        basePickId: pickRegistry.nextId,
      };
      // Register each instance for picking
      for (let i = 0; i < initialTransforms.length; i++) {
        const instancePickId = pickRegistry.nextId++;
        pickRegistry.map.set(instancePickId, {
          entry,
          instanceIndex: i,
          attrs: [{ type: 'onClick', handler: () => node.handler(BigInt(i)) }]
        });
      }

      bindings.push({
        type: 'instanced',
        extract: node.extract,
        handler: node.handler,
        lastCount: initialTransforms.length,
        target: entry,
        pickRegistry,  // Need access to update pick registry on instance count change
      });

      renderList.push(entry);
      break;
    }

    case 'batched': {
      // Batched group: collect children, merge at render time
      const children = [];
      // Children in batched group don't get individual pickIds
      const tempRegistry = { nextId: pickRegistry.nextId, map: new Map() };
      for (const child of node.children) {
        collectNode(child, null, children, bindings, model, tempRegistry, lights, animateNodes);
      }
      const entry = {
        type: 'batched',
        material: node.material,
        transform: overrideTransform || node.transform,
        children,
        // Merged geometry will be computed at render time
        mergedVAO: null,
        mergedCount: 0,
      };
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
        // Also update baseOffset on any child animate entries (compose transforms)
        if (b.childAnimEntries) {
          for (const anim of b.childAnimEntries) {
            anim.baseOffset = newVal;
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
    } else if (b.type === 'instanced') {
      // Re-extract transforms from model
      const scottTransforms = b.extract(newModel);
      const newTransforms = listToArray(scottTransforms).map(interpretTransform);

      // Update transforms
      b.target.transforms = newTransforms;
      b.target.instancesDirty = true;  // Rebuild instance buffer at next render

      // Handle instance count changes: update pick registry
      if (newTransforms.length !== b.lastCount) {
        const registry = b.pickRegistry;
        // Remove old pick IDs
        for (let i = 0; i < b.lastCount; i++) {
          registry.map.delete(b.target.basePickId + i);
        }
        // Add new pick IDs
        for (let i = 0; i < newTransforms.length; i++) {
          const instancePickId = b.target.basePickId + i;
          registry.map.set(instancePickId, {
            entry: b.target,
            instanceIndex: i,
            attrs: [{ type: 'onClick', handler: () => b.handler(BigInt(i)) }]
          });
        }
        b.lastCount = newTransforms.length;
      }
      dirty = true;
    } else if (b.type === 'children') {
      // bindChildren: rebuild children when model changes
      const scottChildren = b.extract(newModel);
      const childrenArray = listToArray(scottChildren);

      // Remove old entries from renderList, pickRegistry, lights
      const renderList = b.renderListRef;
      const pickRegistry = b.pickRegistryRef;
      const lights = b.lightsRef;

      // Remove old render entries
      renderList.splice(b.renderStartIdx, b.renderCount);

      // Remove old lights
      lights.splice(b.lightsStartIdx, b.lightsCount);

      // Remove old pick entries - collect pick IDs to delete
      const pickIdsToDelete = [];
      for (const [pickId, entry] of pickRegistry.map.entries()) {
        // Check if this pick entry belongs to our old children (rough heuristic)
        if (pickId >= b.pickStartSize) {
          pickIdsToDelete.push(pickId);
        }
      }
      for (const pickId of pickIdsToDelete) {
        pickRegistry.map.delete(pickId);
      }

      // Rebuild children at the same position
      const newRenderStartIdx = b.renderStartIdx;
      const newLightsStartIdx = b.lightsStartIdx;
      const newPickStartSize = pickRegistry.map.size;

      // Collect new children
      const tempRenderList = [];
      const tempLights = [];
      for (const scottChild of childrenArray) {
        const interpretedChild = interpretSceneNode(scottChild);
        collectNode(interpretedChild, null, tempRenderList, b.bindings, newModel, pickRegistry, tempLights, []);
      }

      // Insert new entries into renderList and lights
      renderList.splice(newRenderStartIdx, 0, ...tempRenderList);
      lights.splice(newLightsStartIdx, 0, ...tempLights);

      // Update binding with new counts
      b.renderCount = tempRenderList.length;
      b.lightsCount = tempLights.length;
      b.pickStartSize = newPickStartSize;

      dirty = true;
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
function tickAnimateNodes(animateNodes, timeSeconds, hoveredId) {
  for (const anim of animateNodes) {
    // For hover-only animations, accumulate time only when hovered
    let effectiveTime = timeSeconds;
    if (anim.hoverOnly) {
      const isHovered = anim.hoverPickIds.has(hoveredId);
      if (isHovered) {
        // Accumulate time delta
        const dt = anim.lastTimestamp !== null ? (timeSeconds - anim.lastTimestamp) : 0;
        anim.accumTime += dt;
        anim.lastTimestamp = timeSeconds;
      } else {
        // Not hovered — freeze, reset timestamp so we recalculate delta on re-hover
        anim.lastTimestamp = null;
      }
      effectiveTime = anim.accumTime;
    }

    const scottTransform = anim.timeFn(effectiveTime);
    const rawTransform = interpretTransform(scottTransform);

    // Compose with base offset from parent bindTransform (if any)
    const newTransform = anim.baseOffset
      ? { pos: { x: rawTransform.pos.x + anim.baseOffset.pos.x,
                  y: rawTransform.pos.y + anim.baseOffset.pos.y,
                  z: rawTransform.pos.z + anim.baseOffset.pos.z },
          rot: rawTransform.rot, scale: rawTransform.scale }
      : rawTransform;

    for (const entry of anim.targets) {
      entry.transform = newTransform;
    }
    // Update positions of any lights that were children of this animate node
    if (anim.lightIndices) {
      for (const idx of anim.lightIndices) {
        const lt = anim.lightsRef[idx];
        if (lt.position) lt.position = newTransform.pos;
        else if (lt.pos) lt.pos = newTransform.pos;  // spot lights use .pos
      }
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
      // Textured material (Phong-lit with texture sampling)
      const prog = programs.tex;
      gl.useProgram(prog.program);
      gl.uniformMatrix4fv(prog.uniforms.proj, false, programs._projMat);
      gl.uniformMatrix4fv(prog.uniforms.view, false, programs._viewMat);
      gl.uniformMatrix4fv(prog.uniforms.model, false, modelMat);
      const t = mat.tint;
      gl.uniform4f(prog.uniforms.color, t.r, t.g, t.b, t.a);
      gl.uniform1f(prog.uniforms.shininess, 32.0);
      gl.uniform3f(prog.uniforms.cameraPos, cameraPos.x, cameraPos.y, cameraPos.z);
      uploadLights(gl, prog, lights);
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
  } else if (entry.type === 'instanced') {
    // Instanced rendering: draw many instances with a single draw call
    const mat = entry.material;
    const geo = getOrCreateGeometry(gl, geoCache, entry.geometry);

    // Create or update instance buffer
    if (!entry.instanceBuffer || entry.instancesDirty) {
      if (entry.instanceBuffer) {
        updateInstanceBuffer(gl, entry.instanceBuffer.buffer, entry.transforms);
        entry.instanceBuffer.count = entry.transforms.length;
      } else {
        entry.instanceBuffer = createInstanceBuffer(gl, entry.transforms);
      }
      entry.instancesDirty = false;
    }

    if (entry.instanceBuffer.count === 0) return;

    // Use instanced phong shader for lit materials, or fallback to unlit
    const prog = programs.instancedPhong || programs.phong;
    const c = mat.color || mat.tint || { r: 1, g: 1, b: 1, a: 1 };
    gl.useProgram(prog.program);
    gl.uniformMatrix4fv(prog.uniforms.proj, false, programs._projMat);
    gl.uniformMatrix4fv(prog.uniforms.view, false, programs._viewMat);
    gl.uniform4f(prog.uniforms.color, c.r, c.g, c.b, c.a);
    gl.uniform1f(prog.uniforms.shininess, mat.shininess || 32.0);
    gl.uniform3f(prog.uniforms.cameraPos, cameraPos.x, cameraPos.y, cameraPos.z);
    uploadLights(gl, prog, lights);

    // Bind geometry VAO and set up instance attributes
    gl.bindVertexArray(geo.vao);
    setupInstanceAttributes(gl, entry.instanceBuffer.buffer);

    // Draw all instances
    gl.drawElementsInstanced(
      gl.TRIANGLES,
      geo.count,
      gl.UNSIGNED_SHORT,
      0,
      entry.instanceBuffer.count
    );

    // Cleanup
    disableInstanceAttributes(gl);
    gl.bindVertexArray(null);

  } else if (entry.type === 'batched') {
    // Batched rendering: merge children's geometry into single draw call
    // For now, just render children individually (full batching is future work)
    const tfm = entry.transform;
    const groupMat = parentMat
      ? mat4Multiply(parentMat, mat4FromTRS(tfm.pos, tfm.rot, tfm.scale))
      : mat4FromTRS(tfm.pos, tfm.rot, tfm.scale);

    for (const child of entry.children) {
      // Override child's material with batch material
      if (child.type === 'mesh') {
        const savedMat = child.material;
        child.material = entry.material;
        renderEntry(gl, programs, geoCache, texCache, fontCache, child, groupMat, lights, cameraPos);
        child.material = savedMat;
      } else {
        renderEntry(gl, programs, geoCache, texCache, fontCache, child, groupMat, lights, cameraPos);
      }
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

    // Use own pickId or inherited from parent group
    const effectivePickId = entry.pickId ?? entry._groupPickId;
    if (effectivePickId != null) {
      const geo = getOrCreateGeometry(gl, geoCache, entry.geometry);
      const idColor = pickIdToRGB(effectivePickId);

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

    // If the group itself has a pickId (interactiveGroup), render children with that ID
    const groupPickId = entry.pickId;
    for (const child of entry.children) {
      // Pass group's pickId to children for picking
      if (groupPickId != null && child.pickId == null) {
        child._groupPickId = groupPickId;
      }
      renderPickEntry(gl, pickProg, geoCache, child, groupMat);
    }
  } else if (entry.type === 'text') {
    // Text picking: render text quads with pick color
    const effectivePickId = entry.pickId ?? entry._groupPickId;
    if (effectivePickId != null && entry.textVAO && entry.textVAO.vao && entry.textVAO.count > 0) {
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

      const idColor = pickIdToRGB(effectivePickId);
      gl.uniformMatrix4fv(pickProg.uniforms.model, false, finalMat);
      gl.uniform3f(pickProg.uniforms.objectId, idColor.r, idColor.g, idColor.b);

      gl.bindVertexArray(entry.textVAO.vao);
      gl.drawElements(gl.TRIANGLES, entry.textVAO.count, gl.UNSIGNED_SHORT, 0);
      gl.bindVertexArray(null);
    }
  }
}

/**
 * Render instanced entries into the pick buffer.
 * Uses instanced pick shader to encode basePickId + instanceIndex per pixel.
 */
function renderInstancedPick(gl, instancedPickProg, geoCache, entry, projMat, viewMat) {
  if (entry.type !== 'instanced' || !entry.basePickId || !entry.instanceBuffer) return;

  const geo = getOrCreateGeometry(gl, geoCache, entry.geometry);
  if (!geo || entry.instanceBuffer.count === 0) return;

  gl.useProgram(instancedPickProg.program);
  gl.uniformMatrix4fv(instancedPickProg.uniforms.proj, false, projMat);
  gl.uniformMatrix4fv(instancedPickProg.uniforms.view, false, viewMat);
  gl.uniform1i(instancedPickProg.uniforms.basePickId, entry.basePickId);

  gl.bindVertexArray(geo.vao);
  setupInstanceAttributes(gl, entry.instanceBuffer.buffer);

  gl.drawElementsInstanced(
    gl.TRIANGLES,
    geo.count,
    gl.UNSIGNED_SHORT,
    0,
    entry.instanceBuffer.count
  );

  disableInstanceAttributes(gl);
  gl.bindVertexArray(null);
}

/**
 * Render the pick buffer — all interactive objects with unique ID colors.
 */
function renderPickBuffer(gl, pickProg, instancedPickProg, pickFB, geoCache, renderList, projMat, viewMat) {
  gl.bindFramebuffer(gl.FRAMEBUFFER, pickFB.fb);
  gl.viewport(0, 0, pickFB.width, pickFB.height);
  gl.clearColor(0, 0, 0, 1);  // ID 0 = background
  gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
  gl.enable(gl.DEPTH_TEST);

  // First pass: render non-instanced pickable objects
  gl.useProgram(pickProg.program);
  gl.uniformMatrix4fv(pickProg.uniforms.proj, false, projMat);
  gl.uniformMatrix4fv(pickProg.uniforms.view, false, viewMat);

  for (const entry of renderList) {
    if (entry.type !== 'instanced') {
      renderPickEntry(gl, pickProg, geoCache, entry, null);
    }
  }

  // Second pass: render instanced objects (if shader available)
  if (instancedPickProg) {
    for (const entry of renderList) {
      if (entry.type === 'instanced') {
        renderInstancedPick(gl, instancedPickProg, geoCache, entry, projMat, viewMat);
      }
    }
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

  // Compile shaders (unlit + phong + pbr + textured + picking + instanced)
  let programs;
  let pickProg;
  let instancedPhongProg;
  let instancedPickProg;
  try {
    programs = {
      unlit: createProgram(gl),
      phong: createPhongProgram(gl),
      pbr:   createPbrProgram(gl),
      tex:   createTexProgram(gl),
      text:  createTextRenderProgram(gl),
      instancedPhong: createInstancedPhongProgram(gl),
      _projMat: null,
      _viewMat: null,
    };
    pickProg = createPickProgram(gl);
    instancedPickProg = createInstancedPickProgram(gl);
  } catch(e) {
    console.error('[reactive-gl] Shader compilation failed:', e.message);
    return;
  }
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
  console.log('[GL] pickRegistry size:', pickRegistry.map.size, 'hasPickables:', hasPickables);
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
      tickAnimateNodes(animateNodes, timestamp / 1000.0, hoveredId);
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
      renderPickBuffer(gl, pickProg, instancedPickProg, pickFB, geoCache, renderList, projMat, viewMat);
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
    renderPickBuffer(gl, pickProg, instancedPickProg, pickFB, geoCache, renderList, projMat, viewMat);
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
  let dragState = null; // { pickId, startPoint: Vec3, viewMat, projMat } — active drag
  let didDrag = false;  // true if mousemove occurred during drag — suppresses click

  function ensurePickBuffer() {
    if (pickDirty && pickFB) {
      console.log('[GL] rendering pick buffer, renderList length:', renderList.length);
      renderPickBuffer(gl, pickProg, instancedPickProg, pickFB, geoCache, renderList, projMat, viewMat);
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
    const ray = screenToRay(event.clientX, event.clientY, canvas, projMat, viewMat);
    if (!ray) return null;
    // Use rayPickEntries which correctly handles group parent transforms
    const result = rayPickEntries(ray, renderList, pickRegistry);
    if (result && result.pickId === pickId) return result.point;
    // Fallback: if the closest hit is a different object, still try to find our pickId
    // by scanning all hits (rare case when objects overlap)
    return rayPickForId(ray, renderList, pickId);
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
      // Suppress click if a drag just occurred (mousedown → mousemove → mouseup → click)
      if (didDrag) { didDrag = false; return; }
      ensurePickBuffer();
      const id = getPickIdAt(e);
      console.log('[GL] click at', e.offsetX, e.offsetY, 'pickId:', id, 'registry size:', pickRegistry.map.size);
      if (!dispatch || id === 0) return;
      const entry = pickRegistry.map.get(id);
      console.log('[GL] entry:', entry);
      if (!entry) return;

      for (const attr of entry.attrs) {
        console.log('[GL] attr:', attr);
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
      if (!dispatch) return;
      const isMiddle = e.button === 1;

      ensurePickBuffer();
      const id = getPickIdAt(e);

      let targetId = id;
      let targetEntry = id !== 0 ? pickRegistry.map.get(id) : null;

      // Determine which attr type to use based on button and available attrs
      let attrType;
      if (isMiddle) {
        attrType = 'onMiddleDrag';
      } else {
        // Left button: prefer onScreenDrag (screen-space orbit), fallback to onDrag (world-space)
        if (targetEntry && targetEntry.attrs.some(a => a.type === 'onScreenDrag')) {
          attrType = 'onScreenDrag';
        } else if (targetEntry && targetEntry.attrs.some(a => a.type === 'onDrag')) {
          attrType = 'onDrag';
        } else {
          attrType = 'onScreenDrag'; // will try fallback below
        }
      }

      // Fallback: if picked object lacks the attr, search all entries
      if (!targetEntry || !targetEntry.attrs.some(a => a.type === attrType)) {
        for (const [eid, entry] of pickRegistry.map) {
          if (entry.attrs.some(a => a.type === attrType)) {
            targetId = eid;
            targetEntry = entry;
            break;
          }
        }
      }

      if (!targetEntry || targetId === 0) return;

      // Start drag if entry has the right attr type
      for (const attr of targetEntry.attrs) {
        if (attr.type === attrType) {
          if (attrType === 'onScreenDrag' || attrType === 'onMiddleDrag') {
            // Screen-space drag: store pixel coordinates, no raycasting needed
            dragState = {
              pickId: targetId,
              startPoint: { x: e.clientX, y: e.clientY, z: 0 },
              attrType: attrType
            };
            e.preventDefault();
          } else {
            // World-space drag (onDrag): raycast to floor plane
            let point;
            if (id !== 0) {
              point = getRayHitAt(e, id);
            } else {
              const ray = screenToRay(e.clientX, e.clientY, canvas, projMat, viewMat);
              if (ray && Math.abs(ray.dir.y) > 1e-10) {
                const t = -ray.origin.y / ray.dir.y;
                if (t >= 0) point = rayAt(ray, t);
              }
            }
            if (point) {
              dragState = {
                pickId: targetId,
                startPoint: point,
                dragViewMat: viewMat.slice(),
                dragProjMat: projMat.slice(),
                attrType: attrType
              };
              e.preventDefault();
            }
          }
          break;
        }
      }
    });

    // Prevent middle-click auto-scroll
    canvas.addEventListener('auxclick', (e) => { if (e.button === 1) e.preventDefault(); });

    canvas.addEventListener('mousemove', (e) => {
      // Handle active drag
      if (dragState && dispatch) {
        didDrag = true;

        if (dragState.attrType === 'onScreenDrag' || dragState.attrType === 'onMiddleDrag') {
          // Screen-space drag: pass pixel coordinates directly as Vec3 {x, y, z:0}
          const currentPoint = { x: e.clientX, y: e.clientY, z: 0 };
          const entry = pickRegistry.map.get(dragState.pickId);
          if (entry) {
            for (const attr of entry.attrs) {
              if (attr.type === dragState.attrType) {
                dispatch(attr.handler(dragState.startPoint)(currentPoint));
              }
            }
          }
        } else {
          // World-space drag (onDrag) — use snapshotted matrices
          const ray = screenToRay(e.clientX, e.clientY, canvas, dragState.dragProjMat, dragState.dragViewMat);
          if (ray) {
            const denom = ray.dir.y;
            if (Math.abs(denom) > 1e-10) {
              const t = (dragState.startPoint.y - ray.origin.y) / denom;
              if (t >= 0) {
                const currentPoint = rayAt(ray, t);
                const entry = pickRegistry.map.get(dragState.pickId);
                if (entry) {
                  for (const attr of entry.attrs) {
                    if (attr.type === dragState.attrType) {
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
      if (!dispatch) return;
      e.preventDefault();
      ensurePickBuffer();
      const id = getPickIdAt(e);
      const dispatched = new Set();
      // Per-object scroll (color-picked object under cursor)
      if (id !== 0) {
        const entry = pickRegistry.map.get(id);
        if (entry) {
          for (const attr of entry.attrs) {
            if (attr.type === 'onScroll') {
              dispatch(attr.handler(e.deltaY));
              dispatched.add(id);
            }
          }
        }
      }
      // Always also dispatch to ALL other objects with onScroll (canvas-level zoom)
      for (const [eid, entry] of pickRegistry.map) {
        if (dispatched.has(eid)) continue;
        for (const attr of entry.attrs) {
          if (attr.type === 'onScroll') {
            dispatch(attr.handler(e.deltaY));
            dispatched.add(eid);
          }
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
  // Lock CSS size to the initial layout size to prevent resize loops.
  // Without explicit CSS width/height, setting canvas.width changes intrinsic
  // CSS size, which triggers ResizeObserver again → exponential growth.
  let cssLocked = false;
  function handleResize() {
    const dpr = window.devicePixelRatio || 1;
    const rect = canvas.getBoundingClientRect();

    // Lock CSS dimensions on first resize to prevent feedback loop
    if (!cssLocked && rect.width > 0 && rect.height > 0) {
      canvas.style.width = rect.width + 'px';
      canvas.style.height = rect.height + 'px';
      cssLocked = true;
    }

    const drawW = Math.round(rect.width * dpr);
    const drawH = Math.round(rect.height * dpr);

    // Skip zero-size (element not yet laid out) or unchanged
    if (drawW <= 0 || drawH <= 0) return;
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
