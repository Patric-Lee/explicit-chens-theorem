import PlattPointSubsetKernel
import PlattPointPackets.S2B000208
import PlattPointPackets.S2B000209
import PlattPointPackets.S2B000210
import PlattPointPackets.S2B000211
import PlattPointPackets.S2B000212
import PlattGlobalGrid.S7B000045
namespace ChenEffective.PlattWindow.PointCovers.S7B000045
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000208.points ++ ChenEffective.PlattWindow.PointPackets.S2B000209.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000210.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000211.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000212.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000045.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000045.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000045
