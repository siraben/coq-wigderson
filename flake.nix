{
  description = "Coq Wigderson development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/566e53c2ad750c84f6d31f9ccb9d00f823165550";
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
            coq_8_19
            coqPackages_8_19.coq-hammer
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
