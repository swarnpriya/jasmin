{ stdenv, fetchFromGitHub, coqPackages }:

let inherit (coqPackages) coq; in

let mathcomp = coqPackages.mathcomp-algebra or coqPackages.mathcomp; in

let rev = "1020e1c19e9f56ff1d97d5e1b158d74f92bf63cb"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "1p5hzvk3fxck1i0n8ai7j96rwrbd7slnpfb79923j02zk0crj6yq";
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
