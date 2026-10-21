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
        "lib/reduced.gd",
        "lib/automizer-sequence.gd",
    ],
));

# # MANAGE THE ORDERING
# AutoDoc( rec( 
#     autodoc := rec(
#         scan_dirs := []
#     ),
#     scaffold := rec(
#         includes := [ 
#             "_Chapter_ProtoEssentialSubgroups.xml",
#             "_Chapter_ProtoEssentialChecks.xml",
#             "_Chapter_AutomizerSequences.xml",
#         ],
#         bib := "FusionSystems.bib"
#     )
# ));
