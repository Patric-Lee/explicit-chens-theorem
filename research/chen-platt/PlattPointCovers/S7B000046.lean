import PlattPointSubsetKernel
import PlattPointPackets.S2B000212
import PlattPointPackets.S2B000213
import PlattPointPackets.S2B000214
import PlattPointPackets.S2B000215
import PlattPointPackets.S2B000216
import PlattPointPackets.S2B000217
import PlattGlobalGrid.S7B000046
namespace ChenEffective.PlattWindow.PointCovers.S7B000046
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000212.points ++ ChenEffective.PlattWindow.PointPackets.S2B000213.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000214.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000215.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000216.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000217.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000046.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000046.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000046
