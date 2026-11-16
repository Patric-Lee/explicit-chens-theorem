import PlattGlobalGridKernel
import PlattGlobalGrid.S5B000008
import PlattGlobalGrid.S5B000009
import PlattGlobalGrid.S5B000010
import PlattGlobalGrid.S5B000011
import PlattGlobalGrid.S5B000012
import PlattGlobalGrid.S5B000013
import PlattGlobalGrid.S5B000014
import PlattGlobalGrid.S5B000015
import PlattGlobalGrid.S5B000016
import PlattGlobalGrid.S5B000017
import PlattGlobalGrid.S5B000018
import PlattGlobalGrid.S5B000019
import PlattGlobalGrid.S5B000020
import PlattGlobalGrid.S5B000021
import PlattGlobalGrid.S5B000022
import PlattGlobalGrid.S5B000023
import PlattGlobalGrid.S5B000024
import PlattGlobalGrid.S5B000025
import PlattGlobalGrid.S5B000026
import PlattGlobalGrid.S5B000027
import PlattGlobalGrid.S5B000028
import PlattGlobalGrid.S5B000029
import PlattGlobalGrid.S5B000030
import PlattGlobalGrid.S5B000031
import PlattGlobalGrid.S5B000032
import PlattGlobalGrid.S5B000033
import PlattGlobalGrid.S5B000034
import PlattGlobalGrid.S5B000035
import PlattGlobalGrid.S5B000036
import PlattGlobalGrid.S5B000037
import PlattGlobalGrid.S5B000038
import PlattGlobalGrid.S5B000039
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S5B000008.points ++ ChenEffective.PlattWindow.GlobalGrid.S5B000009.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000010.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000011.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000012.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000013.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000014.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000015.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000016.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000017.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000018.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000019.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000020.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000021.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000022.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000023.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000024.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000025.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000026.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000027.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000028.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000029.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000030.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000031.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000032.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000033.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000034.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000035.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000036.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000037.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000038.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000039.points)
theorem certified : GridWindowCertificate 242101248 314533376 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S5B000008.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000009.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000010.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000011.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000012.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000013.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000014.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000015.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000016.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000017.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000018.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000019.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000020.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000021.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000022.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000023.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000024.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000025.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000026.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000027.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000028.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000029.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000030.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000031.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000032.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000033.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000034.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000035.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000036.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000037.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000038.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000039.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0015
