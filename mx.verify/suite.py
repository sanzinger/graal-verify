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
                "version" : "942bc81f277e3c7568d339637c5578831f64d360",
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
