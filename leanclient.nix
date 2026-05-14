{
  buildPythonPackage,
  fetchFromGitHub,
  setuptools,
  hatchling,
  orjson,
  tqdm,
  psutil,
}:
let version = "0.10.0"; in
buildPythonPackage {
    inherit version;
  pname = "leanclient";
    pyproject = true;

  src = fetchFromGitHub {
    owner = "oOo0oOo";
    repo = "leanclient";
    rev  = "v${version}";
    hash = "sha256-v6Z2uC3cnGRp+0xuX79hqPz95xxZ4qYNx5sHBrykI/M=";
  };

  build-system = [hatchling ];

  dependencies = [ 
  orjson
  tqdm
  psutil];

  pythonImportsCheck = [ "leanclient" ];
}