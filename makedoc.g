#
# FusionSystems: Utilities for computing fusion systems
#
# This file is a script which compiles the package manual.
#
LoadPackage("AutoDoc");

# FROM 'gd' to 'xml'
AutoDoc( rec( 
    scaffold := true, 
    bib := "FusionSystems.bib",
    autodoc := true,
    files := [
        # "misc.gd",
        "lib/proto-essentials.gd",
        "lib/proto-essential-checks.gd",
        "lib/automizer-sequence.gd"
    ],
));
