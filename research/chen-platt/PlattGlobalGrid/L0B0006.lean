import PlattGlobalGridKernel
import PlattGlobalGrid.S2B000074
import PlattGlobalGrid.S2B000075
import PlattGlobalGrid.S2B000076
import PlattGlobalGrid.S2B000077
import PlattGlobalGrid.S2B000078
import PlattGlobalGrid.S2B000079
import PlattGlobalGrid.S2B000080
import PlattGlobalGrid.S2B000081
import PlattGlobalGrid.S2B000082
import PlattGlobalGrid.S2B000083
import PlattGlobalGrid.S2B000084
import PlattGlobalGrid.S2B000085
import PlattGlobalGrid.S2B000086
import PlattGlobalGrid.S2B000087
import PlattGlobalGrid.S2B000088
import PlattGlobalGrid.S2B000089
import PlattGlobalGrid.S2B000090
import PlattGlobalGrid.S2B000091
import PlattGlobalGrid.S2B000092
import PlattGlobalGrid.S2B000093
import PlattGlobalGrid.S2B000094
import PlattGlobalGrid.S2B000095
import PlattGlobalGrid.S2B000096
import PlattGlobalGrid.S2B000097
import PlattGlobalGrid.S2B000098
import PlattGlobalGrid.S2B000099
import PlattGlobalGrid.S2B000100
import PlattGlobalGrid.S2B000101
import PlattGlobalGrid.S2B000102
import PlattGlobalGrid.S2B000103
import PlattGlobalGrid.S2B000104
import PlattGlobalGrid.S2B000105
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S2B000074.points ++ ChenEffective.PlattWindow.GlobalGrid.S2B000075.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000076.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000077.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000078.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000079.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000080.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000081.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000082.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000083.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000084.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000085.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000086.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000087.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000088.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000089.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000090.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000091.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000092.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000093.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000094.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000095.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000096.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000097.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000098.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000099.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000100.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000101.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000102.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000103.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000104.points) ++ ChenEffective.PlattWindow.GlobalGrid.S2B000105.points)
theorem certified : GridWindowCertificate 22386304 29449088 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S2B000074.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000075.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000076.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000077.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000078.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000079.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000080.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000081.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000082.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000083.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000084.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000085.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000086.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000087.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000088.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000089.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000090.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000091.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000092.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000093.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000094.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000095.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000096.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000097.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000098.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000099.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000100.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000101.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000102.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000103.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000104.certified) ChenEffective.PlattWindow.GlobalGrid.S2B000105.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0006
