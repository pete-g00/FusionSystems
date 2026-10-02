#
# FusionSystems: Utilities for computing fusion systems
#
# This file contains package meta data. For additional information on
# the meaning and correct usage of these fields, please consult the
# manual of the "Example" package as well as the comments in its
# PackageInfo.g file.
#
SetPackageInfo( rec(

PackageName := "FusionSystems",
Subtitle := "Utilities for computing fusion systems",
Version := "0.1",
Date := "15/10/2026", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

Persons := [
  rec(
    FirstNames := "Josh",
    LastName := "Bridges",
    WWWHome := "https://www.birmingham.ac.uk/staff/profiles/maths/phd-students/bridges-joshua",
    # Email := "...",
    IsAuthor := true,
    IsMaintainer := true,
    #PostalAddress := TODO,
    #Place := TODO,
    Institution := "University of Birmingham",
  ),
  # rec(
  #   FirstNames := "David",
  #   LastName := "Burrell",
  #   WWWHome := "https://people.clas.ufl.edu/davidburrell/",
  #   Email := "davidburrell@ufl.edu",
  #   IsAuthor := true,
  #   IsMaintainer := true,
  #   #PostalAddress := TODO,
  #   #Place := TODO,
  #   Institution := "University of Florida",
  # ),
  rec(
    FirstNames := "Pete",
    LastName := "Gautam",
    # WWWHome := "",
    Email := "pratyush.gautam@manchester.ac.uk",
    IsAuthor := true,
    IsMaintainer := true,
    #PostalAddress := TODO,
    #Place := TODO,
    Institution := "University of Manchester",
  ),
  # rec(
  #   FirstNames := "Justin",
  #   LastName := "Lynd",
  #   WWWHome := "https://userweb.ucs.louisiana.edu/~jxl7583/",
  #   Email := "lynd@louisiana.edu",
  #   IsAuthor := true,
  #   IsMaintainer := true,
  #   #PostalAddress := TODO,
  #   #Place := TODO,
  #   Institution := "University of Louisiana",
  # ),
],

#SourceRepository := rec( Type := "TODO", URL := "URL" ),
#IssueTrackerURL := "TODO",
PackageWWWHome := "https://TODO/",
PackageInfoURL := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL     := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL     := Concatenation( ~.PackageWWWHome,
                                 "/", ~.PackageName, "-", ~.Version ),

ArchiveFormats := ".tar.gz",

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "submitted"     for packages submitted for the refereeing
##    "deposited"     for packages for which the GAP developers agreed
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages
##    "other"         for all other packages
##
Status := "dev",

AbstractHTML   :=  "",

PackageDoc := rec(
  BookName  := "FusionSystems",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "A GAP package on fusion systems",
),

Dependencies := rec(
  GAP := ">= 4.7",
  NeededOtherPackages := [["anupq",">=3.2.1"],["autpgrp",">=1.10.2"],["format",">=1.4.3"],["crisp",">=1.4.5"]],
  SuggestedOtherPackages := [],
  ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",

#Keywords := [ "TODO" ],

));

