import PlattGlobalGridKernel
import PlattGlobalGrid.L0B0000
import PlattGlobalGrid.L0B0001
import PlattGlobalGrid.L0B0002
import PlattGlobalGrid.L0B0003
import PlattGlobalGrid.L0B0004
import PlattGlobalGrid.L0B0005
import PlattGlobalGrid.L0B0006
import PlattGlobalGrid.L0B0007
import PlattGlobalGrid.L0B0008
import PlattGlobalGrid.L0B0009
import PlattGlobalGrid.L0B0010
import PlattGlobalGrid.L0B0011
import PlattGlobalGrid.L0B0012
import PlattGlobalGrid.L0B0013
import PlattGlobalGrid.L0B0014
import PlattGlobalGrid.L0B0015
import PlattGlobalGrid.L0B0016
import PlattGlobalGrid.L0B0017
import PlattGlobalGrid.L0B0018
import PlattGlobalGrid.L0B0019
import PlattGlobalGrid.L0B0020
import PlattGlobalGrid.L0B0021
import PlattGlobalGrid.L0B0022
import PlattGlobalGrid.L0B0023
import PlattGlobalGrid.L0B0024
import PlattGlobalGrid.L0B0025
import PlattGlobalGrid.L0B0026
import PlattGlobalGrid.L0B0027
import PlattGlobalGrid.L0B0028
import PlattGlobalGrid.L0B0029
namespace ChenEffective.PlattWindow.GlobalGrid.L1B0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.L0B0000.points ++ ChenEffective.PlattWindow.GlobalGrid.L0B0001.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0002.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0003.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0004.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0005.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0006.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0007.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0008.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0009.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0010.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0011.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0012.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0013.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0014.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0015.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0016.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0017.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0018.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0019.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0020.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0021.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0022.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0023.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0024.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0025.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0026.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0027.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0028.points) ++ ChenEffective.PlattWindow.GlobalGrid.L0B0029.points)
theorem certified : GridWindowCertificate 4000000 10000000000 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.L0B0000.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0001.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0002.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0003.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0004.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0005.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0006.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0007.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0008.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0009.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0010.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0011.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0012.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0013.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0014.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0015.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0016.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0017.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0018.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0019.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0020.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0021.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0022.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0023.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0024.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0025.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0026.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0027.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0028.certified) ChenEffective.PlattWindow.GlobalGrid.L0B0029.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L1B0000
