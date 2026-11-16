import PlattGlobalGridKernel
import PlattGlobalGrid.S1B000000
import PlattGlobalGrid.S1B000001
import PlattGlobalGrid.S1B000002
import PlattGlobalGrid.S1B000003
import PlattGlobalGrid.S1B000004
import PlattGlobalGrid.S1B000005
import PlattGlobalGrid.S1B000006
import PlattGlobalGrid.S1B000007
import PlattGlobalGrid.S1B000008
import PlattGlobalGrid.S1B000009
import PlattGlobalGrid.S1B000010
import PlattGlobalGrid.S1B000011
import PlattGlobalGrid.S1B000012
import PlattGlobalGrid.S1B000013
import PlattGlobalGrid.S1B000014
import PlattGlobalGrid.S1B000015
import PlattGlobalGrid.S1B000016
import PlattGlobalGrid.S1B000017
import PlattGlobalGrid.S1B000018
import PlattGlobalGrid.S1B000019
import PlattGlobalGrid.S1B000020
import PlattGlobalGrid.S1B000021
import PlattGlobalGrid.S1B000022
import PlattGlobalGrid.S1B000023
import PlattGlobalGrid.S1B000024
import PlattGlobalGrid.S1B000025
import PlattGlobalGrid.S1B000026
import PlattGlobalGrid.S1B000027
import PlattGlobalGrid.S1B000028
import PlattGlobalGrid.S1B000029
import PlattGlobalGrid.S1B000030
import PlattGlobalGrid.S1B000031
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S1B000000.points ++ ChenEffective.PlattWindow.GlobalGrid.S1B000001.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000002.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000003.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000004.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000005.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000006.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000007.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000008.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000009.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000010.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000011.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000012.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000013.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000014.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000015.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000016.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000017.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000018.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000019.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000020.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000021.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000022.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000023.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000024.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000025.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000026.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000027.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000028.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000029.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000030.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000031.points)
theorem certified : GridWindowCertificate 4000000 5495616 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S1B000000.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000001.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000002.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000003.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000004.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000005.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000006.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000007.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000008.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000009.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000010.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000011.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000012.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000013.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000014.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000015.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000016.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000017.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000018.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000019.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000020.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000021.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000022.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000023.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000024.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000025.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000026.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000027.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000028.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000029.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000030.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000031.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0000
