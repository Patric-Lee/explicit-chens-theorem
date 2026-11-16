import PlattGlobalGridKernel
import PlattGlobalGrid.S1B000096
import PlattGlobalGrid.S1B000097
import PlattGlobalGrid.S1B000098
import PlattGlobalGrid.S1B000099
import PlattGlobalGrid.S1B000100
import PlattGlobalGrid.S1B000101
import PlattGlobalGrid.S1B000102
import PlattGlobalGrid.S1B000103
import PlattGlobalGrid.S1B000104
import PlattGlobalGrid.S1B000105
import PlattGlobalGrid.S1B000106
import PlattGlobalGrid.S1B000107
import PlattGlobalGrid.S1B000108
import PlattGlobalGrid.S1B000109
import PlattGlobalGrid.S1B000110
import PlattGlobalGrid.S1B000111
import PlattGlobalGrid.S1B000112
import PlattGlobalGrid.S1B000113
import PlattGlobalGrid.S1B000114
import PlattGlobalGrid.S1B000115
import PlattGlobalGrid.S1B000116
import PlattGlobalGrid.S1B000117
import PlattGlobalGrid.S2B000000
import PlattGlobalGrid.S2B000001
import PlattGlobalGrid.S2B000002
import PlattGlobalGrid.S2B000003
import PlattGlobalGrid.S2B000004
import PlattGlobalGrid.S2B000005
import PlattGlobalGrid.S2B000006
import PlattGlobalGrid.S2B000007
import PlattGlobalGrid.S2B000008
import PlattGlobalGrid.S2B000009
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S1B000096.points ++ ChenEffective.PlattWindow.GlobalGrid.S1B000097.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000098.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000099.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000100.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000101.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000102.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000103.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000104.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000105.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000106.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000107.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000108.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000109.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000110.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000111.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000112.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000113.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000114.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000115.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000116.points) ++ ChenEffective.PlattWindow.GlobalGrid.S1B000117.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000000.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000001.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000002.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000003.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000004.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000005.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000006.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000007.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000008.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000009.points)
theorem certified : GridWindowCertificate 9772864 12808640 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S1B000096.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000097.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000098.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000099.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000100.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000101.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000102.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000103.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000104.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000105.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000106.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000107.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000108.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000109.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000110.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000111.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000112.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000113.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000114.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000115.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000116.certified) ChenEffective.PlattWindow.GlobalGrid.S1B000117.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000000.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000001.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000002.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000003.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000004.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000005.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000006.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000007.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000008.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000009.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0003
