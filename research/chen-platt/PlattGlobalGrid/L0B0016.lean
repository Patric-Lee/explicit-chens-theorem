import PlattGlobalGridKernel
import PlattGlobalGrid.S5B000040
import PlattGlobalGrid.S5B000041
import PlattGlobalGrid.S5B000042
import PlattGlobalGrid.S5B000043
import PlattGlobalGrid.S5B000044
import PlattGlobalGrid.S5B000045
import PlattGlobalGrid.S5B000046
import PlattGlobalGrid.S5B000047
import PlattGlobalGrid.S5B000048
import PlattGlobalGrid.S5B000049
import PlattGlobalGrid.S5B000050
import PlattGlobalGrid.S5B000051
import PlattGlobalGrid.S5B000052
import PlattGlobalGrid.S5B000053
import PlattGlobalGrid.S5B000054
import PlattGlobalGrid.S5B000055
import PlattGlobalGrid.S5B000056
import PlattGlobalGrid.S5B000057
import PlattGlobalGrid.S5B000058
import PlattGlobalGrid.S5B000059
import PlattGlobalGrid.S5B000060
import PlattGlobalGrid.S5B000061
import PlattGlobalGrid.S5B000062
import PlattGlobalGrid.S5B000063
import PlattGlobalGrid.S5B000064
import PlattGlobalGrid.S5B000065
import PlattGlobalGrid.S5B000066
import PlattGlobalGrid.S5B000067
import PlattGlobalGrid.S5B000068
import PlattGlobalGrid.S5B000069
import PlattGlobalGrid.S5B000070
import PlattGlobalGrid.S5B000071
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S5B000040.points ++ ChenEffective.PlattWindow.GlobalGrid.S5B000041.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000042.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000043.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000044.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000045.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000046.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000047.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000048.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000049.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000050.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000051.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000052.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000053.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000054.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000055.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000056.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000057.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000058.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000059.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000060.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000061.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000062.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000063.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000064.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000065.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000066.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000067.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000068.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000069.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000070.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000071.points)
theorem certified : GridWindowCertificate 314533376 408632832 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S5B000040.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000041.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000042.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000043.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000044.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000045.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000046.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000047.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000048.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000049.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000050.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000051.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000052.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000053.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000054.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000055.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000056.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000057.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000058.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000059.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000060.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000061.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000062.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000063.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000064.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000065.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000066.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000067.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000068.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000069.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000070.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000071.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0016
