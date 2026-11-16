import PlattGlobalGridKernel
import PlattGlobalGrid.S5B000104
import PlattGlobalGrid.S5B000105
import PlattGlobalGrid.S5B000106
import PlattGlobalGrid.S5B000107
import PlattGlobalGrid.S5B000108
import PlattGlobalGrid.S5B000109
import PlattGlobalGrid.S5B000110
import PlattGlobalGrid.S5B000111
import PlattGlobalGrid.S5B000112
import PlattGlobalGrid.S5B000113
import PlattGlobalGrid.S5B000114
import PlattGlobalGrid.S5B000115
import PlattGlobalGrid.S5B000116
import PlattGlobalGrid.S5B000117
import PlattGlobalGrid.S6B000000
import PlattGlobalGrid.S6B000001
import PlattGlobalGrid.S6B000002
import PlattGlobalGrid.S6B000003
import PlattGlobalGrid.S6B000004
import PlattGlobalGrid.S6B000005
import PlattGlobalGrid.S6B000006
import PlattGlobalGrid.S6B000007
import PlattGlobalGrid.S6B000008
import PlattGlobalGrid.S6B000009
import PlattGlobalGrid.S6B000010
import PlattGlobalGrid.S6B000011
import PlattGlobalGrid.S6B000012
import PlattGlobalGrid.S6B000013
import PlattGlobalGrid.S6B000014
import PlattGlobalGrid.S6B000015
import PlattGlobalGrid.S6B000016
import PlattGlobalGrid.S6B000017
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S5B000104.points ++ ChenEffective.PlattWindow.GlobalGrid.S5B000105.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000106.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000107.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000108.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000109.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000110.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000111.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000112.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000113.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000114.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000115.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000116.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000117.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000000.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000001.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000002.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000003.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000004.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000005.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000006.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000007.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000008.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000009.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000010.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000011.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000012.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000013.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000014.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000015.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000016.points) ++ ChenEffective.PlattWindow.GlobalGrid.S6B000017.points)
theorem certified : GridWindowCertificate 530277376 682838016 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S5B000104.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000105.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000106.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000107.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000108.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000109.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000110.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000111.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000112.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000113.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000114.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000115.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000116.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000117.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000000.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000001.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000002.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000003.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000004.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000005.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000006.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000007.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000008.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000009.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000010.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000011.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000012.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000013.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000014.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000015.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000016.certified) ChenEffective.PlattWindow.GlobalGrid.S6B000017.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0018
