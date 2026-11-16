import PlattPointSubsetKernel
import PlattPointPackets.S2B000252
import PlattPointPackets.S2B000253
import PlattPointPackets.S2B000254
import PlattPointPackets.S2B000255
import PlattPointPackets.S2B000256
import PlattPointPackets.S2B000257
import PlattGlobalGrid.S7B000055
namespace ChenEffective.PlattWindow.PointCovers.S7B000055
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000252.points ++ ChenEffective.PlattWindow.PointPackets.S2B000253.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000254.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000255.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000256.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000257.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000055.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000055.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000055
