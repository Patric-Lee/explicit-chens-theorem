import PlattGlobalGridKernel
import PlattGlobalGrid.S8B000070
import PlattGlobalGrid.S8B000071
import PlattGlobalGrid.S8B000072
import PlattGlobalGrid.S8B000073
import PlattGlobalGrid.S8B000074
import PlattGlobalGrid.S8B000075
import PlattGlobalGrid.S8B000076
import PlattGlobalGrid.S8B000077
import PlattGlobalGrid.S8B000078
import PlattGlobalGrid.S8B000079
import PlattGlobalGrid.S8B000080
import PlattGlobalGrid.S8B000081
import PlattGlobalGrid.S8B000082
import PlattGlobalGrid.S8B000083
import PlattGlobalGrid.S8B000084
import PlattGlobalGrid.S8B000085
import PlattGlobalGrid.S8B000086
import PlattGlobalGrid.S8B000087
import PlattGlobalGrid.S8B000088
import PlattGlobalGrid.S8B000089
import PlattGlobalGrid.S8B000090
import PlattGlobalGrid.S8B000091
import PlattGlobalGrid.S8B000092
import PlattGlobalGrid.S8B000093
import PlattGlobalGrid.S8B000094
import PlattGlobalGrid.S8B000095
import PlattGlobalGrid.S8B000096
import PlattGlobalGrid.S8B000097
import PlattGlobalGrid.S8B000098
import PlattGlobalGrid.S8B000099
import PlattGlobalGrid.S8B000100
import PlattGlobalGrid.S8B000101
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S8B000070.points ++ ChenEffective.PlattWindow.GlobalGrid.S8B000071.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000072.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000073.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000074.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000075.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000076.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000077.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000078.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000079.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000080.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000081.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000082.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000083.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000084.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000085.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000086.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000087.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000088.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000089.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000090.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000091.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000092.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000093.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000094.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000095.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000096.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000097.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000098.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000099.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000100.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000101.points)
theorem certified : GridWindowCertificate 6874703872 8889968640 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S8B000070.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000071.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000072.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000073.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000074.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000075.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000076.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000077.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000078.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000079.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000080.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000081.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000082.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000083.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000084.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000085.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000086.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000087.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000088.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000089.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000090.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000091.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000092.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000093.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000094.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000095.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000096.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000097.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000098.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000099.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000100.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000101.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0028
