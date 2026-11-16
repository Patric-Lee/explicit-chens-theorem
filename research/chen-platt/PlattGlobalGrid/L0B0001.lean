import PlattGlobalGridKernel
import PlattGlobalGrid.S1B000032
import PlattGlobalGrid.S1B000033
import PlattGlobalGrid.S1B000034
import PlattGlobalGrid.S1B000035
import PlattGlobalGrid.S1B000036
import PlattGlobalGrid.S1B000037
import PlattGlobalGrid.S1B000038
import PlattGlobalGrid.S1B000039
import PlattGlobalGrid.S1B000040
import PlattGlobalGrid.S1B000041
import PlattGlobalGrid.S1B000042
import PlattGlobalGrid.S1B000043
import PlattGlobalGrid.S1B000044
import PlattGlobalGrid.S1B000045
import PlattGlobalGrid.S1B000046
import PlattGlobalGrid.S1B000047
import PlattGlobalGrid.S1B000048
import PlattGlobalGrid.S1B000049
import PlattGlobalGrid.S1B000050
import PlattGlobalGrid.S1B000051
import PlattGlobalGrid.S1B000052
import PlattGlobalGrid.S1B000053
import PlattGlobalGrid.S1B000054
import PlattGlobalGrid.S1B000055
import PlattGlobalGrid.S1B000056
import PlattGlobalGrid.S1B000057
import PlattGlobalGrid.S1B000058
import PlattGlobalGrid.S1B000059
import PlattGlobalGrid.S1B000060
import PlattGlobalGrid.S1B000061
import PlattGlobalGrid.S1B000062
import PlattGlobalGrid.S1B000063
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S1B000032.points ++ ChenEffective.PlattWindow.GlobalGrid.S1B000033.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000034.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000035.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000036.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000037.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000038.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000039.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000040.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000041.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000042.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000043.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000044.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000045.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000046.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000047.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000048.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000049.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000050.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000051.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000052.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000053.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000054.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000055.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000056.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000057.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000058.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000059.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000060.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000061.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000062.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000063.points)
theorem certified : GridWindowCertificate 5495616 7365952 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S1B000032.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000033.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000034.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000035.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000036.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000037.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000038.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000039.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000040.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000041.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000042.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000043.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000044.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000045.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000046.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000047.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000048.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000049.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000050.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000051.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000052.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000053.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000054.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000055.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000056.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000057.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000058.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000059.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000060.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000061.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000062.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000063.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0001
