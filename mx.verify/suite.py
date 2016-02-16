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
                "name" : "graal-core",
                "version" : "1f226be60fffa2263b8084923b3c59d1e708e0f6",
                "urls" : [
                    {"url" : "https://github.com/graalvm/graal-core", "kind" : "git"},
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
        "graal-core:GRAAL_TEST",
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
	"graal-core:GRAAL_COMPILER",
	"graal-core:GRAAL_HOTSPOT",
	"at.sanzinger.boolector",
      ],
      "annotationProcessors" : [
        "graal-core:GRAAL_NODEINFO_PROCESSOR",
        "graal-core:GRAAL_REPLACEMENTS_VERIFIER",
        "graal-core:GRAAL_OPTIONS_PROCESSOR",
        "graal-core:GRAAL_SERVICEPROVIDER_PROCESSOR",
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
        "graal-core:GRAAL_HOTSPOT",
      ],
    },
  },
}
