import PlattPointSubsetKernel
import PlattPointPackets.S1B000300
import PlattPointPackets.S1B000301
import PlattPointPackets.S1B000302
import PlattPointPackets.S1B000303
import PlattGlobalGrid.S5B000116
namespace ChenEffective.PlattWindow.PointCovers.S5B000116
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000300.points ++ ChenEffective.PlattWindow.PointPackets.S1B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000303.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000116.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000116.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000116
