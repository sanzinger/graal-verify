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
                "version" : "a2bf47587cc1241cc8833906c12d9004e05a0a15",
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
  },
}
