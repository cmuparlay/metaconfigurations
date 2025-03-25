(lang dune 3.8)

(using coq 0.8)

(name metaconfigurations)

(generate_opam_files)

(license MIT)

(authors "Anonymous")

(maintainers "Anonymous")

(source
 (github anonymous/anonymous))

(package
 (name metaconfigurations)
 (synopsis "Mechanization of metaconfigurations tracking")
 (depends
  (coq
   (>= 8.16))
  (coq-stdpp
   (>= 1.10.0))))
