import PlattPointSubsetKernel
import PlattPointPackets.S5B000100
import PlattPointPackets.S5B000101
import PlattPointPackets.S5B000102
import PlattPointPackets.S5B000103
import PlattPointPackets.S5B000104
import PlattPointPackets.S5B000105
import PlattPointPackets.S5B000106
import PlattPointPackets.S5B000107
import PlattPointPackets.S5B000108
import PlattPointPackets.S5B000109
import PlattPointPackets.S5B000110
import PlattPointPackets.S5B000111
import PlattGlobalGrid.S8B000046
namespace ChenEffective.PlattWindow.PointCovers.S8B000046
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000100.points ++ ChenEffective.PlattWindow.PointPackets.S5B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000106.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000108.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000111.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000046.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000046.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000046
