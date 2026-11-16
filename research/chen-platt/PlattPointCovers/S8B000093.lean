import PlattPointSubsetKernel
import PlattPointPackets.S7B000095
import PlattPointPackets.S7B000096
import PlattPointPackets.S7B000097
import PlattPointPackets.S7B000098
import PlattPointPackets.S7B000099
import PlattPointPackets.S7B000100
import PlattPointPackets.S7B000101
import PlattPointPackets.S7B000102
import PlattPointPackets.S7B000103
import PlattPointPackets.S7B000104
import PlattPointPackets.S7B000105
import PlattPointPackets.S7B000106
import PlattPointPackets.S7B000107
import PlattPointPackets.S7B000108
import PlattPointPackets.S7B000109
import PlattPointPackets.S7B000110
import PlattPointPackets.S7B000111
import PlattGlobalGrid.S8B000093
namespace ChenEffective.PlattWindow.PointCovers.S8B000093
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000095.points ++ ChenEffective.PlattWindow.PointPackets.S7B000096.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000097.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000099.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000100.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000106.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000108.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000111.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000093.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000093.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000093
