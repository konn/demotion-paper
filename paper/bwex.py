# -*- coding: utf-8 -*-
"""
    pygments.styles.bwex
    ~~~~~~~~~~~~~~~~~~~~

    Simple black/white only style + Hiromi Ishii's special.
"""

from pygments.style import Style
from pygments.token import Keyword, Name, Comment, String, Error, \
     Operator, Generic

class BwexStyle(Style):

    background_color = "#ffffff"
    default_style = ""

    styles = {
        Comment:                   "italic",
        Comment.Preproc:           "italic",

        Keyword:                   "bold",
        Keyword.Pseudo:            "nobold",
        Keyword.Type:              "nobold",

        Operator.Word:             "bold",

        Name.Class:                "bold underline",
        Name.Namespace:            "bold",
        Name.Exception:            "bold",
        Name.Entity:               "bold",
        Name.Tag:                  "bold",

        String:                    "italic",
        String.Interpol:           "bold",
        String.Escape:             "bold",

        Generic.Heading:           "bold",
        Generic.Subheading:        "bold",
        Generic.Emph:              "italic",
        Generic.Strong:            "bold",
        Generic.Prompt:            "bold",

        Error:                     "border:#FF0000"
    }
