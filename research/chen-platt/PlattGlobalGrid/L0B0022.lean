import PlattGlobalGridKernel
import PlattGlobalGrid.S6B000114
import PlattGlobalGrid.S6B000115
import PlattGlobalGrid.S6B000116
import PlattGlobalGrid.S6B000117
import PlattGlobalGrid.S7B000000
import PlattGlobalGrid.S7B000001
import PlattGlobalGrid.S7B000002
import PlattGlobalGrid.S7B000003
import PlattGlobalGrid.S7B000004
import PlattGlobalGrid.S7B000005
import PlattGlobalGrid.S7B000006
import PlattGlobalGrid.S7B000007
import PlattGlobalGrid.S7B000008
import PlattGlobalGrid.S7B000009
import PlattGlobalGrid.S7B000010
import PlattGlobalGrid.S7B000011
import PlattGlobalGrid.S7B000012
import PlattGlobalGrid.S7B000013
import PlattGlobalGrid.S7B000014
import PlattGlobalGrid.S7B000015
import PlattGlobalGrid.S7B000016
import PlattGlobalGrid.S7B000017
import PlattGlobalGrid.S7B000018
import PlattGlobalGrid.S7B000019
import PlattGlobalGrid.S7B000020
import PlattGlobalGrid.S7B000021
import PlattGlobalGrid.S7B000022
import PlattGlobalGrid.S7B000023
import PlattGlobalGrid.S7B000024
import PlattGlobalGrid.S7B000025
import PlattGlobalGrid.S7B000026
import PlattGlobalGrid.S7B000027
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S6B000114.points ++ ChenEffective.PlattWindow.GlobalGrid.S6B000115.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000116.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000117.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000000.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000001.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000002.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000003.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000004.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000005.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000006.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000007.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000008.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000009.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000010.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000011.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000012.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000013.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000014.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000015.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000016.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000017.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000018.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000019.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000020.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000021.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000022.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000023.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000024.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000025.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000026.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000027.points)
theorem certified : GridWindowCertificate 1484267520 1909486592 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S6B000114.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000115.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000116.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000117.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000000.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000001.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000002.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000003.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000004.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000005.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000006.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000007.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000008.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000009.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000010.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000011.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000012.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000013.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000014.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000015.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000016.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000017.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000018.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000019.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000020.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000021.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000022.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000023.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000024.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000025.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000026.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000027.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0022
