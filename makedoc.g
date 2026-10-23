LoadPackage("AutoDoc");

# FROM 'gd' to 'xml'
AutoDoc( rec(
    scaffold := true,
    bib := "FusionSystems.bib",
    autodoc := rec(
        # the chapters appear in this order
        files := [
            "doc/intro.autodoc",
            "lib/proto-essentials.gd",
            "lib/proto-essential-checks.gd",
            "lib/reduced.gd",
            "lib/automizer-sequence.gd",
            "lib/misc.gd",
        ],
        scan_dirs := [],
    ),
    extract_examples := true,
));
