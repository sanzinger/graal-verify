from mx_jvmci import jdkDeployedDists
from mx_graal_8 import GraalJDKDeployedDist

jdkDeployedDists += [GraalJDKDeployedDist('GRAAL_VERIFY', compilers=["graal-verify"])]
