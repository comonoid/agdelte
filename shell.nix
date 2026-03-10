# Compatibility wrapper for non-flake nix users.
# Preferred: `nix develop` (uses flake.nix)
# Fallback:  `nix-shell`  (uses this file)
{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    pkgs.nodejs_20
    pkgs.agda

    (pkgs.haskellPackages.ghcWithPackages (p: with p; [
      # Server runtime
      network
      text
      bytestring
      stm
      containers
      async
      directory

      # Web framework
      warp
      wai
      wai-websockets
      http-types
      websockets

      # Misc
      case-insensitive
      unix

      # Testing
      hspec
    ]))
  ];
}
