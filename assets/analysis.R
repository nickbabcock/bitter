library(tidyverse)
library(scales)

is_bitter <- function(fn) {
  fn %in% c("bitter-auto", "bitter-manual", "bitter-unchecked")
}

pal <- c(
  "bitter-auto"      = "#1B9E77",
  "bitter-manual"    = "#D95F02",
  "bitter-unchecked" = "#7570B3",
  "bitbuffer"        = "#E7298A",
  "bitcursor"        = "#66A61E",
  "bitreader"        = "#E6AB02",
  "bitstream-io"     = "#A6761D",
  "bitvec"           = "#666666"
)

# Run from the assets directory so the relative path resolves.
df <- read_csv("./bitter-benchmark-data.csv") %>%
  mutate(
    fn = factor(`function`, levels = names(pal)),
    line = if_else(is_bitter(`function`), "bitter", "other"),
    latency = (iteration_count * 1000) / sample_measured_value,
  )

ggplot(df, aes(value, latency, color = fn, linetype = line)) +
  stat_summary(fun = mean, geom = "line", linewidth = 1.2) +
  scale_color_manual("Bit reader", values = pal) +
  scale_linetype_manual(values = c(bitter = "solid", other = "dotted"), guide = "none") +
  scale_y_continuous(breaks = pretty_breaks(10)) +
  scale_x_continuous(breaks = c(seq(1, 64, 4), 64)) +
  labs(
    title = "Rust Bit Readers Performance Comparison",
    subtitle = "Performance measured in reads per nanosecond (higher is better)",
    caption = "Bitter implementations marked with solid lines",
    y = "Reads per ns",
    x = "Read size (bits)"
  ) +
  theme_minimal()
ggsave('bench-bit-reads.png', width = 9, height = 5, dpi = 100)
