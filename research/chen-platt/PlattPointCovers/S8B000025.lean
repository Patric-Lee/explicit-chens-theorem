import PlattPointSubsetKernel
import PlattPointPackets.S4B000202
import PlattPointPackets.S4B000203
import PlattPointPackets.S4B000204
import PlattPointPackets.S4B000205
import PlattPointPackets.S4B000206
import PlattPointPackets.S4B000207
import PlattPointPackets.S4B000208
import PlattPointPackets.S4B000209
import PlattPointPackets.S4B000210
import PlattPointPackets.S4B000211
import PlattGlobalGrid.S8B000025
namespace ChenEffective.PlattWindow.PointCovers.S8B000025
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000202.points ++ ChenEffective.PlattWindow.PointPackets.S4B000203.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000204.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000205.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000206.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000207.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000208.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000209.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000210.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000211.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000025.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000025.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000025
