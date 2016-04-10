var app = angular.module('graalverify', ['ui.bootstrap']);

app.controller("resultpresentation", function($scope) {
  $scope.result = [];
  $scope.fileLoaded = function(payload){
    $scope.result = JSON.parse(payload);
    $scope.$apply();
  }
});

app.directive("fileread", [ function() {
  return {
    scope : {
      fileread : "&"
    },
    link : function(scope, element, attributes) {
      element.bind("change", function(changeEvent) {
        var reader = new FileReader();
        reader.onload = function(loadEvent) {
          scope.fileread({
            payload : loadEvent.target.result
          })
        }
        reader.readAsText(changeEvent.target.files[0]);
      });
    }
  }
} ]);