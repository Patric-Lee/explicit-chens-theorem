import PlattPointSubsetKernel
import PlattPointPackets.S1B000281
import PlattPointPackets.S1B000282
import PlattPointPackets.S1B000283
import PlattGlobalGrid.S5B000107
namespace ChenEffective.PlattWindow.PointCovers.S5B000107
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000281.points ++ ChenEffective.PlattWindow.PointPackets.S1B000282.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000283.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000107.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000107.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000107
