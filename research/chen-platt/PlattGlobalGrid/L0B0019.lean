import PlattGlobalGridKernel
import PlattGlobalGrid.S6B000018
import PlattGlobalGrid.S6B000019
import PlattGlobalGrid.S6B000020
import PlattGlobalGrid.S6B000021
import PlattGlobalGrid.S6B000022
import PlattGlobalGrid.S6B000023
import PlattGlobalGrid.S6B000024
import PlattGlobalGrid.S6B000025
import PlattGlobalGrid.S6B000026
import PlattGlobalGrid.S6B000027
import PlattGlobalGrid.S6B000028
import PlattGlobalGrid.S6B000029
import PlattGlobalGrid.S6B000030
import PlattGlobalGrid.S6B000031
import PlattGlobalGrid.S6B000032
import PlattGlobalGrid.S6B000033
import PlattGlobalGrid.S6B000034
import PlattGlobalGrid.S6B000035
import PlattGlobalGrid.S6B000036
import PlattGlobalGrid.S6B000037
import PlattGlobalGrid.S6B000038
import PlattGlobalGrid.S6B000039
import PlattGlobalGrid.S6B000040
import PlattGlobalGrid.S6B000041
import PlattGlobalGrid.S6B000042
import PlattGlobalGrid.S6B000043
import PlattGlobalGrid.S6B000044
import PlattGlobalGrid.S6B000045
import PlattGlobalGrid.S6B000046
import PlattGlobalGrid.S6B000047
import PlattGlobalGrid.S6B000048
import PlattGlobalGrid.S6B000049
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S6B000018.points ++ ChenEffective.PlattWindow.GlobalGrid.S6B000019.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000020.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000021.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000022.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000023.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000024.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000025.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000026.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000027.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000028.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000029.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000030.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000031.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000032.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000033.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000034.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000035.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000036.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000037.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000038.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000039.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000040.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000041.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000042.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000043.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000044.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000045.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000046.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000047.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000048.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000049.points)
theorem certified : GridWindowCertificate 682838016 884391424 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S6B000018.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000019.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000020.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000021.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000022.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000023.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000024.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000025.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000026.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000027.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000028.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000029.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000030.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000031.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000032.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000033.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000034.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000035.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000036.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000037.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000038.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000039.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000040.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000041.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000042.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000043.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000044.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000045.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000046.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000047.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000048.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000049.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0019
