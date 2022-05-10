{ src ? import ./nix/sources.nix
, pkgs ? import src.nixpkgs {} }:
with pkgs;

mkShell {
  packages = [
    coq_8_13
    coqPackages_8_13.coqhammer
    vampire
    eprover
    (if stdenv.isDarwin then
      ((import (builtins.fetchTarball {
        url = "https://github.com/NixOS/nixpkgs/archive/a3e1e9271e0ff87309d44f9817baadb09b305757.tar.gz";
      }) {}).cvc4)
    else cvc4)
    (z3-tptp.overrideAttrs (oA: {
      installPhase = oA.installPhase + ''
    ln -s "z3_tptp5" "$out/bin/z3_tptp"
  '';
    }))
  ];
}
