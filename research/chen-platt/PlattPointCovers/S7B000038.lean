import PlattPointSubsetKernel
import PlattPointPackets.S2B000180
import PlattPointPackets.S2B000181
import PlattPointPackets.S2B000182
import PlattPointPackets.S2B000183
import PlattPointPackets.S2B000184
import PlattGlobalGrid.S7B000038
namespace ChenEffective.PlattWindow.PointCovers.S7B000038
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000180.points ++ ChenEffective.PlattWindow.PointPackets.S2B000181.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000182.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000183.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000184.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000038.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000038.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000038
