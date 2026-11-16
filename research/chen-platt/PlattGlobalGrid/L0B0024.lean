import PlattGlobalGridKernel
import PlattGlobalGrid.S7B000060
import PlattGlobalGrid.S7B000061
import PlattGlobalGrid.S7B000062
import PlattGlobalGrid.S7B000063
import PlattGlobalGrid.S7B000064
import PlattGlobalGrid.S7B000065
import PlattGlobalGrid.S7B000066
import PlattGlobalGrid.S7B000067
import PlattGlobalGrid.S7B000068
import PlattGlobalGrid.S7B000069
import PlattGlobalGrid.S7B000070
import PlattGlobalGrid.S7B000071
import PlattGlobalGrid.S7B000072
import PlattGlobalGrid.S7B000073
import PlattGlobalGrid.S7B000074
import PlattGlobalGrid.S7B000075
import PlattGlobalGrid.S7B000076
import PlattGlobalGrid.S7B000077
import PlattGlobalGrid.S7B000078
import PlattGlobalGrid.S7B000079
import PlattGlobalGrid.S7B000080
import PlattGlobalGrid.S7B000081
import PlattGlobalGrid.S7B000082
import PlattGlobalGrid.S7B000083
import PlattGlobalGrid.S7B000084
import PlattGlobalGrid.S7B000085
import PlattGlobalGrid.S7B000086
import PlattGlobalGrid.S7B000087
import PlattGlobalGrid.S7B000088
import PlattGlobalGrid.S7B000089
import PlattGlobalGrid.S7B000090
import PlattGlobalGrid.S7B000091
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S7B000060.points ++ ChenEffective.PlattWindow.GlobalGrid.S7B000061.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000062.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000063.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000064.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000065.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000066.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000067.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000068.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000069.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000070.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000071.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000072.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000073.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000074.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000075.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000076.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000077.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000078.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000079.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000080.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000081.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000082.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000083.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000084.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000085.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000086.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000087.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000088.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000089.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000090.points) ++ ChenEffective.PlattWindow.GlobalGrid.S7B000091.points)
theorem certified : GridWindowCertificate 2471340032 3197102080 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S7B000060.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000061.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000062.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000063.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000064.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000065.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000066.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000067.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000068.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000069.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000070.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000071.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000072.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000073.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000074.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000075.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000076.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000077.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000078.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000079.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000080.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000081.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000082.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000083.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000084.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000085.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000086.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000087.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000088.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000089.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000090.certified) ChenEffective.PlattWindow.GlobalGrid.S7B000091.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0024
