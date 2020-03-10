with import <nixpkgs> {};

let coqPackages = coqPackages_8_9; in

let coqword = callPackage ./coqword.nix { inherit coqPackages; }; in

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ coqPackages.coq coqword coqPackages.dpdgraph ]
    ++ (with python3Packages; [ python pyyaml ])
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild batteries menhir merlin zarith mpfr camlidl apron ppl])
    ;
}
