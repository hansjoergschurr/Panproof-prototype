{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "panproof";

  hardeningDisable = [ "all" ];
  buildInputs = with pkgs; [
    pkg-config zlib cabal-install ghc
  ];
}
