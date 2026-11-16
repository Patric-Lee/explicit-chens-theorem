import PlattGlobalGridKernel
import PlattGlobalGrid.S4B000094
import PlattGlobalGrid.S4B000095
import PlattGlobalGrid.S4B000096
import PlattGlobalGrid.S4B000097
import PlattGlobalGrid.S4B000098
import PlattGlobalGrid.S4B000099
import PlattGlobalGrid.S4B000100
import PlattGlobalGrid.S4B000101
import PlattGlobalGrid.S4B000102
import PlattGlobalGrid.S4B000103
import PlattGlobalGrid.S4B000104
import PlattGlobalGrid.S4B000105
import PlattGlobalGrid.S4B000106
import PlattGlobalGrid.S4B000107
import PlattGlobalGrid.S4B000108
import PlattGlobalGrid.S4B000109
import PlattGlobalGrid.S4B000110
import PlattGlobalGrid.S4B000111
import PlattGlobalGrid.S4B000112
import PlattGlobalGrid.S4B000113
import PlattGlobalGrid.S4B000114
import PlattGlobalGrid.S4B000115
import PlattGlobalGrid.S4B000116
import PlattGlobalGrid.S4B000117
import PlattGlobalGrid.S5B000000
import PlattGlobalGrid.S5B000001
import PlattGlobalGrid.S5B000002
import PlattGlobalGrid.S5B000003
import PlattGlobalGrid.S5B000004
import PlattGlobalGrid.S5B000005
import PlattGlobalGrid.S5B000006
import PlattGlobalGrid.S5B000007
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S4B000094.points ++ ChenEffective.PlattWindow.GlobalGrid.S4B000095.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000096.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000097.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000098.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000099.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000100.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000101.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000102.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000103.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000104.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000105.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000106.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000107.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000108.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000109.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000110.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000111.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000112.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000113.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000114.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000115.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000116.points) ++ ChenEffective.PlattWindow.GlobalGrid.S4B000117.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000000.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000001.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000002.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000003.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000004.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000005.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000006.points) ++ ChenEffective.PlattWindow.GlobalGrid.S5B000007.points)
theorem certified : GridWindowCertificate 187728640 242101248 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S4B000094.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000095.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000096.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000097.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000098.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000099.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000100.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000101.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000102.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000103.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000104.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000105.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000106.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000107.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000108.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000109.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000110.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000111.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000112.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000113.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000114.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000115.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000116.certified) ChenEffective.PlattWindow.GlobalGrid.S4B000117.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000000.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000001.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000002.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000003.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000004.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000005.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000006.certified) ChenEffective.PlattWindow.GlobalGrid.S5B000007.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0014
