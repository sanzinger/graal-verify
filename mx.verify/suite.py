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
                "version" : "aa321bfb2a65e9edc72cfff668517d70475ea303",
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
        "graal:GRAAL_TEST"
      ],
      "workingSets" : "Verification",
    },

    "at.sanzinger.graal.verify" : {
      "subDir" : "gverify",
      "sourceDirs" : ["src"],
      "javaCompliance" : "1.8",
      "workingSets" : "Verification",
    },

  },

  "distributions" : {
  },
}
