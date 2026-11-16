import PlattGlobalGridKernel
import PlattGlobalGrid.S8B000102
import PlattGlobalGrid.S8B000103
import PlattGlobalGrid.S8B000104
import PlattGlobalGrid.S8B000105
import PlattGlobalGrid.S8B000106
import PlattGlobalGrid.S8B000107
import PlattGlobalGrid.S8B000108
import PlattGlobalGrid.S8B000109
import PlattGlobalGrid.S8B000110
import PlattGlobalGrid.S8B000111
import PlattGlobalGrid.S8B000112
import PlattGlobalGrid.S8B000113
import PlattGlobalGrid.S8B000114
import PlattGlobalGrid.S8B000115
import PlattGlobalGrid.S8B000116
namespace ChenEffective.PlattWindow.GlobalGrid.L0B0029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := ((((((((((((((ChenEffective.PlattWindow.GlobalGrid.S8B000102.points ++ ChenEffective.PlattWindow.GlobalGrid.S8B000103.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000104.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000105.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000106.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000107.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000108.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000109.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000110.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000111.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000112.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000113.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000114.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000115.points) ++ ChenEffective.PlattWindow.GlobalGrid.S8B000116.points)
theorem certified : GridWindowCertificate 8889968640 10000000000 points := GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (GridWindowCertificate.append (ChenEffective.PlattWindow.GlobalGrid.S8B000102.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000103.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000104.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000105.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000106.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000107.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000108.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000109.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000110.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000111.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000112.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000113.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000114.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000115.certified) ChenEffective.PlattWindow.GlobalGrid.S8B000116.certified
#print axioms certified
end ChenEffective.PlattWindow.GlobalGrid.L0B0029
