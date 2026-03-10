{
  description = "Agdelte — Reactive UI Framework with Dependent Types in Agda";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.${system}.default = pkgs.mkShell {
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
      };
    };
}
