module.exports = {
  env: {
    browser: true,
    es2022: true,
    node: true,
  },
  parserOptions: {
    ecmaVersion: 2022,
    sourceType: 'module',
  },
  rules: {
    // Errors
    'no-undef': 'error',
    'no-unused-vars': ['warn', { argsIgnorePattern: '^_' }],
    'no-constant-condition': ['error', { checkLoops: false }],

    // Style (relaxed for generated code compatibility)
    'semi': ['warn', 'always'],
    'quotes': ['warn', 'single', { avoidEscape: true }],
    'indent': 'off', // Let editor handle

    // Best practices
    'eqeqeq': ['warn', 'smart'],
    'no-var': 'warn',
    'prefer-const': 'warn',
  },
  ignorePatterns: [
    '_build/**',
    'node_modules/**',
    '*.min.js',
  ],
};
