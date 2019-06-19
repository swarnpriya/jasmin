{ stdenv, fetchFromGitHub, coqPackages }:

let inherit (coqPackages) coq; in

let mathcomp = coqPackages.mathcomp-algebra or coqPackages.mathcomp; in

let rev = "6dc43c6be9458f8c3fc7ba16e2c6580a3c72ed21"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "16a4v5k1qgajf37ylqhm0fm91snxia1p1b54b85247d2nssccp0c";
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
