import PlattPointSubsetKernel
import PlattPointPackets.S2B000200
import PlattPointPackets.S2B000201
import PlattPointPackets.S2B000202
import PlattPointPackets.S2B000203
import PlattPointPackets.S2B000204
import PlattGlobalGrid.S7B000043
namespace ChenEffective.PlattWindow.PointCovers.S7B000043
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000200.points ++ ChenEffective.PlattWindow.PointPackets.S2B000201.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000202.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000203.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000204.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000043.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000043.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000043
