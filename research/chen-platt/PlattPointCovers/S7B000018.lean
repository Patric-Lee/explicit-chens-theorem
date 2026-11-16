import PlattPointSubsetKernel
import PlattPointPackets.S2B000106
import PlattPointPackets.S2B000107
import PlattPointPackets.S2B000108
import PlattPointPackets.S2B000109
import PlattGlobalGrid.S7B000018
namespace ChenEffective.PlattWindow.PointCovers.S7B000018
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000106.points ++ ChenEffective.PlattWindow.PointPackets.S2B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000108.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000109.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000018.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000018.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000018
