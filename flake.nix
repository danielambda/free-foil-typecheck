{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-25.11";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    free-foil.url = "github:fizruk/free-foil";
    free-foil.flake = false;
  };

  outputs = inputs@{ nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [inputs.haskell-flake.flakeModule];
      perSystem = { self', config, pkgs, ... }: {
        haskellProjects.default = {
          autoWire = ["packages" "apps"];

          packages.free-foil.source = inputs.free-foil + /haskell/free-foil;
          settings.free-foil.check = false;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [config.haskellProjects.default.outputs.devShell];
          packages = with pkgs; [
            nixd
            hpack
          ];
        };

        packages.default = self'.packages.free-foil-typecheck;
      };
    };
}
