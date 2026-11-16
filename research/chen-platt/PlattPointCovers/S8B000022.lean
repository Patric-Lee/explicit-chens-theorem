import PlattPointSubsetKernel
import PlattPointPackets.S4B000175
import PlattPointPackets.S4B000176
import PlattPointPackets.S4B000177
import PlattPointPackets.S4B000178
import PlattPointPackets.S4B000179
import PlattPointPackets.S4B000180
import PlattPointPackets.S4B000181
import PlattPointPackets.S4B000182
import PlattPointPackets.S4B000183
import PlattPointPackets.S4B000184
import PlattGlobalGrid.S8B000022
namespace ChenEffective.PlattWindow.PointCovers.S8B000022
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000175.points ++ ChenEffective.PlattWindow.PointPackets.S4B000176.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000177.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000178.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000179.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000180.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000181.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000182.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000183.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000184.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000022.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000022.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000022
