suite = {
  "mxversion" : "5.5.6",
  "name" : "verify",
  "url" : "http://openjdk.java.net/projects/graal",
  "developer" : {
    "name" : "Stefan Anzinger",
    "email" : "stefan.anzinger@gmail.com",
    "organization" : "Stefan Anzinger",
    "organizationUrl" : "http://anzinger.net",
  },
  "repositories" : {
  },

  "imports" : {
    "suites": [
            {
                "name" : "graal",
                "version" : "964f28c04d7bbae2b7dfad8ed7003140d92b84ba",
                "urls" : [
                    {"url" : "http://lafo.ssw.uni-linz.ac.at/hg/graal-compiler", "kind" : "hg"},
                ]
            },
    ]
  },


  "libraries" : {
  },


  "projects" : {


    "at.sanzinger.graal.verify.test" : {
      "subDir" : "gverify",
      "sourceDirs" : ["src"],
      "javaCompliance" : "1.8",
      "dependencies" : [
        "graal:GRAAL_TEST",
	"at.sanzinger.graal.verify",
      ],
      "workingSets" : "Verification",
    },

    "at.sanzinger.graal.verify" : {
      "subDir" : "gverify",
      "sourceDirs" : ["src"],
      "javaCompliance" : "1.8",
      "workingSets" : "Verification",
      "dependencies" : [
	"graal:GRAAL_COMPILER",
	"graal:GRAAL_HOTSPOT",
	"at.sanzinger.boolector",
      ],
      "annotationProcessors" : [
        "graal:GRAAL_NODEINFO_PROCESSOR",
        "graal:GRAAL_REPLACEMENTS_VERIFIER",
        "graal:GRAAL_OPTIONS_PROCESSOR",
        "graal:GRAAL_SERVICEPROVIDER_PROCESSOR",
      ],
    },

    "at.sanzinger.boolector" : {
      "subDir" : "gverify",
      "sourceDirs" : ["src"],
      "javaCompliance" : "1.8",
      "workingSets" : "Verification",
      "dependencies" : [
      ],
    },

    "at.sanzinger.boolector.test" : {
      "subDir" : "gverify",
      "sourceDirs" : ["src"],
      "javaCompliance" : "1.8",
      "workingSets" : "Verification",
      "dependencies" : [
	"mx:JUNIT",
	"at.sanzinger.boolector",
      ],
    },

  },

  "distributions" : {
    "GRAAL_VERIFY" : {
      "subDir" : "gverify",
      "dependencies" : [
        "at.sanzinger.graal.verify",
      ],
      "distDependencies" : [
        "graal:GRAAL_HOTSPOT",
      ],
    },
  },
}
