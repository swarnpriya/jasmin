{ stdenv, fetchFromGitHub, coqPackages }:

let inherit (coqPackages) coq; in

let mathcomp = coqPackages.mathcomp-algebra or coqPackages.mathcomp; in

let rev = "14d21c02204d0a59fca9242da39de70ac88e89ed"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "145sc40d3jcbrk7fl2ss08c769idgzcbznk1b9a5jdsba8rx16hp";
  };

  buildInputs = [ coq ];

  propagatedBuildInputs = [ mathcomp ];

  installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

  meta = {
    description = "Yet Another Coq Library on Machine Words";
    license = stdenv.lib.licenses.cecill-b;
    inherit (src.meta) homepage;
    inherit (coq.meta) platforms;
  };
}
