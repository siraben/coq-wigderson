{
  description = "Coq Wigderson development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/103a4c0ae46afa9cf008c30744175315ca38e9f9";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            coq_8_13
            coqPackages_8_13.coqhammer
            vampire
            eprover
            cvc4
            (z3-tptp.overrideAttrs (oA: {
              installPhase = oA.installPhase + ''
                ln -s "z3_tptp5" "$out/bin/z3_tptp"
              '';
            }))
          ];
        };
      });
}