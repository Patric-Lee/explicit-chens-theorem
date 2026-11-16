import PlattPointSubsetKernel
import PlattPointPackets.S2B000299
import PlattPointPackets.S2B000300
import PlattPointPackets.S2B000301
import PlattPointPackets.S2B000302
import PlattPointPackets.S2B000303
import PlattPointPackets.S2B000304
import PlattGlobalGrid.S7B000065
namespace ChenEffective.PlattWindow.PointCovers.S7B000065
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000299.points ++ ChenEffective.PlattWindow.PointPackets.S2B000300.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000303.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000304.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000065.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000065.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000065
