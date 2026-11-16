import PlattGlobalGridKernel
import PlattGlobalGrid.S3B000052
import PlattGlobalGrid.S3B000053
import PlattGlobalGrid.S3B000054
import PlattGlobalGrid.S3B000055
import PlattGlobalGrid.S3B000056
import PlattGlobalGrid.S3B000057
import PlattGlobalGrid.S3B000058
import PlattGlobalGrid.S3B000059
import PlattGlobalGrid.S3B000060
import PlattGlobalGrid.S3B000061
import PlattGlobalGrid.S3B000062
import PlattGlobalGrid.S3B000063
import PlattGlobalGrid.S3B000064
import PlattGlobalGrid.S3B000065
import PlattGlobalGrid.S3B000066
import PlattGlobalGrid.S3B000067
import PlattGlobalGrid.S3B000068
import PlattGlobalGrid.S3B000069
import PlattGlobalGrid.S3B000070
import PlattGlobalGrid.S3B000071
import PlattGlobalGrid.S3B000072
import PlattGlobalGrid.S3B000073
import PlattGlobalGrid.S3B000074
import PlattGlobalGrid.S3B000075
import PlattGlobalGrid.S3B000076
import PlattGlobalGrid.S3B000077
import PlattGlobalGrid.S3B000078
import PlattGlobalGrid.S3B000079
import PlattGlobalGrid.S3B000080
import PlattGlobalGrid.S3B000081
import PlattGlobalGrid.S3B000082
import PlattGlobalGrid.S3B000083
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S3B000052.points ++ ChenEffective.PlattWindow.GlobalGrid.S3B000053.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000054.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000055.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000056.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000057.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000058.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000059.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000060.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000061.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000062.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000063.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000064.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000065.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000066.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000067.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000068.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000069.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000070.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000071.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000072.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000073.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000074.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000075.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000076.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000077.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000078.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000079.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000080.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000081.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000082.points) ++ ChenEffective.PlattWindow.GlobalGrid.S3B000083.points)
theorem certified : GridWindowCertificate 50136064 65329280 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S3B000052.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000053.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000054.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000055.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000056.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000057.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000058.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000059.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000060.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000061.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000062.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000063.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000064.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000065.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000066.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000067.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000068.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000069.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000070.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000071.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000072.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000073.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000074.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000075.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000076.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000077.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000078.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000079.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000080.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000081.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000082.certified) ChenEffective.PlattWindow.GlobalGrid.S3B000083.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0009
