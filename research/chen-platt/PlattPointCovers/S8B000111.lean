import PlattPointSubsetKernel
import PlattPointPackets.S8B000089
import PlattPointPackets.S8B000090
import PlattPointPackets.S8B000091
import PlattPointPackets.S8B000092
import PlattPointPackets.S8B000093
import PlattPointPackets.S8B000094
import PlattPointPackets.S8B000095
import PlattPointPackets.S8B000096
import PlattPointPackets.S8B000097
import PlattPointPackets.S8B000098
import PlattPointPackets.S8B000099
import PlattPointPackets.S8B000100
import PlattPointPackets.S8B000101
import PlattPointPackets.S8B000102
import PlattPointPackets.S8B000103
import PlattPointPackets.S8B000104
import PlattPointPackets.S8B000105
import PlattPointPackets.S8B000106
import PlattPointPackets.S8B000107
import PlattPointPackets.S8B000108
import PlattGlobalGrid.S8B000111
namespace ChenEffective.PlattWindow.PointCovers.S8B000111
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000089.points ++ ChenEffective.PlattWindow.PointPackets.S8B000090.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000091.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000092.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000093.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000094.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000095.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000096.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000097.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000099.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000100.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000106.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000108.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000111.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000111.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000111
