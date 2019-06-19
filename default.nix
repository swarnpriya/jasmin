with import <nixpkgs> {};

let coqPackages = coqPackages_8_8; in

let coqword = callPackage ./coqword.nix { inherit coqPackages; }; in

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ coqPackages.coq coqword ]
    ++ (with python3Packages; [ python pyyaml ])
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild batteries menhir merlin zarith mpfr camlidl apron ppl])
    ;
}
