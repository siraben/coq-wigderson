{ src ? import ./nix/sources.nix
, pkgs ? import src.nixpkgs {} }:
with pkgs;

mkShell {
  packages = [
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
}
