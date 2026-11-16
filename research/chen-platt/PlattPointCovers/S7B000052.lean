import PlattPointSubsetKernel
import PlattPointPackets.S2B000239
import PlattPointPackets.S2B000240
import PlattPointPackets.S2B000241
import PlattPointPackets.S2B000242
import PlattPointPackets.S2B000243
import PlattGlobalGrid.S7B000052
namespace ChenEffective.PlattWindow.PointCovers.S7B000052
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000239.points ++ ChenEffective.PlattWindow.PointPackets.S2B000240.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000241.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000242.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000243.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000052.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000052.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000052
