import PlattPointSubsetKernel
import PlattPointPackets.S2B000138
import PlattPointPackets.S2B000139
import PlattPointPackets.S2B000140
import PlattPointPackets.S2B000141
import PlattGlobalGrid.S7B000027
namespace ChenEffective.PlattWindow.PointCovers.S7B000027
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000138.points ++ ChenEffective.PlattWindow.PointPackets.S2B000139.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000140.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000141.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000027.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000027.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000027
